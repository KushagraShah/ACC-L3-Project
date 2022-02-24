package l3

import scala.collection.mutable.{ Map => MutableMap }

abstract class CPSOptimizer[T <: CPSTreeModule { type Name = Symbol }]
  (val treeModule: T) {
  import treeModule._

  protected def rewrite(tree: Tree): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = size(simplifiedTree) * 3 / 2
    fixedPoint(simplifiedTree, 8) { t => inline(t, maxSize) }
  }

  private case class Count(applied: Int = 0, asValue: Int = 0)

  private case class State(
    census: Map[Name, Count],
    aSubst: Subst[Atom] = emptySubst,
    cSubst: Subst[Name] = emptySubst,
    eInvEnv: Map[(ValuePrimitive, Seq[Atom]), Atom] = Map.empty,
    cEnv: Map[Name, Cnt] = Map.empty,
    fEnv: Map[Name, Fun] = Map.empty) {

    def dead(s: Name): Boolean =
      ! census.contains(s)
    def appliedOnce(s: Name): Boolean =
      census.get(s).contains(Count(applied = 1, asValue = 0))

    def withASubst(from: Atom, to: Atom): State =
      copy(aSubst = aSubst + (from -> aSubst(to)))
    def withASubst(from: Name, to: Atom): State =
      withASubst(AtomN(from), to)
    def withASubst(from: Name, to: Literal): State =
      withASubst(from, AtomL(to))
    def withASubst(from: Seq[Name], to: Seq[Atom]): State =
      copy(aSubst = aSubst ++ (from.map(AtomN) zip to.map(aSubst)))

    def withCSubst(from: Name, to: Name): State =
      copy(cSubst = cSubst + (from -> cSubst(to)))

    def withExp(atom: Atom, prim: ValuePrimitive, args: Seq[Atom]): State =
      copy(eInvEnv = eInvEnv + ((prim, args) -> atom))
    def withExp(name: Name, prim: ValuePrimitive, args: Seq[Atom]): State =
      withExp(AtomN(name), prim, args)

    def withCnts(cnts: Seq[Cnt]): State =
      copy(cEnv = cEnv ++ (cnts.map(_.name) zip cnts))
    def withFuns(funs: Seq[Fun]): State =
      copy(fEnv = fEnv ++ (funs.map(_.name) zip funs))
    
    // Added for arguments
    def withArg(atom: Atom): Atom = atom match {
      case AtomN(name) =>
        val tmp = aSubst.getOrElse(atom, AtomN(cSubst.getOrElse(name, name)))
        tmp
      case _ => atom
    }
  }

  // Shrinking optimizations ------------------------------------------------//

  private def shrink(tree: Tree): Tree =
    shrink(tree, State(census(tree)))

  // Helper functions
  private def litSeq(a: Seq[Atom]) = 
    a.flatMap(_.asLiteral)

  // LetP
  private def help_LetP(letp: LetP, s: State): Tree = letp match {
    case LetP(name, prim, _, body) 
      if (!impure(prim) && s.dead(name)) => { 
        shrink(body,s)
      }

    case LetP(name, prim, lits @ Seq(AtomL(_), AtomL(_)), body) 
      if vEvaluator.isDefinedAt((prim, litSeq(lits)))  => {
        val cf = (vEvaluator)((prim, litSeq(lits)))
        shrink(body, s.withASubst(name, cf))
      }
    
    case LetP(name, this.identity, Seq(AtomN(name_)), body) => {
      shrink(body, s.withCSubst(name, name_))
    }

    case LetP(name, prim, lits @ Seq(AtomL(v1), v2), body) 
      if leftNeutral.contains((v1, prim)) => {
        shrink(body, s.withASubst(name, v2))
      }

    case LetP(name, prim, lits @ Seq(v1, AtomL(v2)), body) 
      if rightNeutral.contains((prim, v2)) => {
        shrink(body, s.withASubst(name, v1))
      }

    case LetP(name, prim, lits @ Seq(a1 @ AtomL(v1), _), body) 
      if leftAbsorbing.contains((v1, prim)) => {
        shrink(body, s.withASubst(name, a1))
      }

    case LetP(name, prim, lits @ Seq(_, a2 @ AtomL(v2)), body) 
      if rightAbsorbing.contains((prim, v2)) => {
        shrink(body, s.withASubst(name, a2))
      }

    case LetP(name, prim, args, body) => {
      val sub_args = args.map(arg => s.withArg(arg))
      s.eInvEnv.get((prim, sub_args)) match {
        case Some(value) => {
          shrink(body, s.withASubst(name, value))
        }
        case None => {
          val state = if (impure(prim) || unstable(prim))
                        s 
                      else 
                        s.withExp(name, prim, sub_args)
          LetP(name, prim, sub_args, shrink(body, state))
        }
      }
    }
  }

  // AppF
  private def help_AppF(appf: AppF, s: State): Tree = appf match {
    case AppF(fun @ AtomN(fName), retC, args) 
      if s.aSubst.contains(fun) => {
        shrink(AppF(s.aSubst(fun), retC, args), s)
      }

    case AppF(fun @ AtomN(fName), retC, args) 
      if s.cSubst.contains(fName) => {
        shrink(AppF(AtomN(s.cSubst(fName)), retC, args), s)
      }

    case appf_ @ AppF(fun @ AtomN(fName), retC, args) => {
      s.fEnv.get(fName) match {
        case Some(Fun(inName, inRet, inArgs, inBody)) => {
          shrink(inBody, s.withASubst(inArgs, args).withCSubst(inRet, retC))
        }

        case None => {
          appf_
        }
      }
    }
  }

  // AppC
  private def help_AppC(appc: AppC, s: State): Tree = appc match {
    case AppC(cnt, args) 
      if s.cSubst.contains(cnt) => {
        shrink(AppC(s.cSubst(cnt), args.map(arg => s.withArg(arg))), s)
      }
    
    case appc_ @ AppC(cnt, args) => {
      s.cEnv.get(cnt) match {
        case Some(Cnt(name, args_, body)) => {
          val sub_args = args.map((arg: Atom) => s.withArg(arg))
          val state = s.withASubst(args_, sub_args)
          shrink(body, state)
        }

        case None => {
          appc_
        }
      }
    }
  }

  // If
  private def help_If(if_t: If, s: State): Tree = if_t match {
    case If(cond, lits @ Seq(AtomL(l1), AtomL(l2)), ct, cf)
      if cEvaluator.isDefinedAt((cond, litSeq(lits))) => {
        val left = (cEvaluator)((cond,  litSeq(lits)))
        shrink(AppC(if(left) ct else cf, Seq()), s)
      }

    case If(cond, Seq(AtomL(BooleanLit(v1)), AtomL(BooleanLit(v2))), ct, cf)
      if sameArgReduceC(cond) => {
        shrink(AppC(if(v1 == v2) ct else cf, Seq()), s)
      }

    case If(cond, Seq(v1, v2), ct, cf)
      if (v1 == v2) => {
        shrink(AppC(if(sameArgReduceC(cond)) ct else cf, Seq()), s)
      }

    case _ => {
      if_t
    }
  }

  // General shrinking step
  private def shrink(tree: Tree, s: State): Tree = tree match {
    case halt @ Halt(atom @ AtomN(name)) => {
      (s.cSubst.get(name), s.aSubst.get(atom)) match {
        case (Some(name_), None) => {
          Halt(AtomN(name_))
        }
        case (None, Some(atom_)) => {
          Halt(atom_)
        }
        case _ => {
          halt
        }
      }
    }

    case LetF(funs, body) => {
      val filt_funs = funs.filter(f => !s.dead(f.name))
      val (unopt_funs, in_funs) = filt_funs.partition(f => !s.appliedOnce(f.name))
      val state = s.withFuns(in_funs)
      val opt_funs: Seq[Fun] = unopt_funs.map{
        case Fun(name, ret, args, body) => {
          Fun(name, ret, args, shrink(body, state))
        }
      }

      if (opt_funs.size > 0) 
        LetF(opt_funs, shrink(body, state))
      else 
        shrink(body, state)
    }

    case LetC(cnts, body) => {
      val filt_cnts = cnts.filter(c => !s.dead(c.name)).map{
        case Cnt(name, args, body) => {
          Cnt(name, args, shrink(body, s))
        }
      }
      val (unopt_cnts, in_cnts) = filt_cnts.partition(c => !s.appliedOnce(c.name))
      val state = s.withCnts(in_cnts)

      if (unopt_cnts.size > 0)
        LetC(unopt_cnts, shrink(body, state))
      else
        shrink(body, state)
    }

    case LetP(name, prim, args, body) => { 
      val sub_args = args.map(arg => s.withArg(arg)) 
      help_LetP(LetP(name, prim, sub_args, body), s)
    }

    case AppF(fun, ret, args) => {
      val sub_args = args.map(arg => s.withArg(arg))
      help_AppF(AppF(fun, s.cSubst.getOrElse(ret, ret), sub_args), s)
    }

    case AppC(cnt, args) => {
      val sub_args = args.map(arg => s.withArg(arg))
      help_AppC(AppC(cnt, sub_args), s)
    }

    case If(prim, args, ct, cf) => {
      val sub_args = args.map(arg => s.withArg(arg))
      help_If(If(prim, sub_args, ct, cf), s)
    }

    case _ => {
      tree
    }
  }

  // (Non-shrinking) inlining ------------------------------------------------//

  private def inline(tree: Tree, maxSize: Int): Tree = {
    def copyT(tree: Tree, subV: Subst[Atom], subC: Subst[Name]): Tree = {
      (tree: @unchecked) match {
        case LetP(name, prim, args, body) =>
          val name1 = name.copy()
          LetP(name1, prim, args map subV,
               copyT(body, subV + (AtomN(name) -> AtomN(name1)), subC))
        case LetC(cnts, body) =>
          val names = cnts map (_.name)
          val names1 = names map (_.copy())
          val subC1 = subC ++ (names zip names1)
          LetC(cnts map (copyC(_, subV, subC1)), copyT(body, subV, subC1))
        case LetF(funs, body) =>
          val names = funs map (_.name)
          val names1 = names map (_.copy())
          val subV1 = subV ++ ((names map AtomN) zip (names1 map AtomN))
          LetF(funs map (copyF(_, subV1, subC)), copyT(body, subV1, subC))
        case AppC(cnt, args) =>
          AppC(subC(cnt), args map subV)
        case AppF(fun, retC, args) =>
          AppF(subV(fun), subC(retC), args map subV)
        case If(cond, args, thenC, elseC) =>
          If(cond, args map subV, subC(thenC), subC(elseC))
        case Halt(arg) =>
          Halt(subV(arg))
      }
    }

    def copyC(cnt: Cnt, subV: Subst[Atom], subC: Subst[Name]): Cnt = {
      val args1 = cnt.args map (_.copy())
      val subV1 = subV ++ ((cnt.args map AtomN) zip (args1 map AtomN))
      Cnt(subC(cnt.name), args1, copyT(cnt.body, subV1, subC))
    }

    def copyF(fun: Fun, subV: Subst[Atom], subC: Subst[Name]): Fun = {
      val retC1 = fun.retC.copy()
      val subC1 = subC + (fun.retC -> retC1)
      val args1 = fun.args map (_.copy())
      val subV1 = subV ++ ((fun.args map AtomN) zip (args1 map AtomN))
      val AtomN(funName1) = subV(AtomN(fun.name))
      Fun(funName1, retC1, args1, copyT(fun.body, subV1, subC1))
    }

    val fibonacci = Seq(1, 2, 3, 5, 8, 13)

    val trees = LazyList.iterate((0, tree), fibonacci.length){ case (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i

      def sameLen[T,U](formalArgs: Seq[T], actualArgs: Seq[U]): Boolean =
        formalArgs.length == actualArgs.length

      // Expand definition ---------------------------
      def inlineT(tree: Tree)(implicit s: State): Tree = tree match {
        case LetP(name, prim, args, body) => {
          LetP(name, prim, args, inlineT(body))
        }
        case LetC(cnts, body) 
          if (cnts.size == 0) => {
            inlineT(body)
          }

        case LetC(cnts, body) => {
          val in_cnts = cnts.map{
            case Cnt(name, args, body) => {
              Cnt(name, args, inlineT(body))
            }
          }
          val filt_cnts = in_cnts.filter(c => (size(c.body) < cntLimit))
          val state = s.withCnts(filt_cnts)

          LetC(in_cnts, inlineT(body)(state))
        }

        case LetF(funs, body) => {
          val in_funs = funs.map{
            case Fun(name, ret, args, body) => {
              Fun(name, ret, args, inlineT(body))
            }
          }
          val filt_funs = in_funs.filter(f => (size(f.body) < funLimit))
          val state = s.withFuns(filt_funs)

          LetF(in_funs, inlineT(body)(state))
        }

        case appc @ AppC(cName, args) => {
          s.cEnv.get(cName) match {
            case Some(Cnt(_, args_, body)) => {
              val aSubst_ = s.aSubst ++ args_.map(AtomN).zip(args)
              copyT(body, aSubst_, s.cSubst)
            }
            case None => {
              appc
            }
          }
        }

        case appf @ AppF(AtomN(fName), f_cnt, args) => {
          s.fEnv.get(fName) match {
            case Some(Fun(_, ret, args_, body)) => {
              val aSubst_ = s.aSubst ++ args_.map(AtomN).zip(args).toMap
              val cSubst_ = s.cSubst + (ret -> f_cnt)
              copyT(body, aSubst_, cSubst_)
            }
            case None => {
              appf
            }
          }
        }

        case _ => {
          tree
        }
      }

      (i + 1, fixedPoint(inlineT(tree)(State(census(tree))))(shrink))
    }

    trees.takeWhile{ case (_, tree) => size(tree) <= maxSize }.last._2
  }

  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]().withDefault(_ => Count())
    val rhs = MutableMap[Name, Tree]()

    def incAppUseN(name: Name): Unit = {
      val currCount = census(name)
      census(name) = currCount.copy(applied = currCount.applied + 1)
      rhs.remove(name).foreach(addToCensus)
    }

    def incAppUseA(atom: Atom): Unit =
      atom.asName.foreach(incAppUseN(_))

    def incValUseN(name: Name): Unit = {
      val currCount = census(name)
      census(name) = currCount.copy(asValue = currCount.asValue + 1)
      rhs.remove(name).foreach(addToCensus)
    }

    def incValUseA(atom: Atom): Unit =
      atom.asName.foreach(incValUseN(_))

    def addToCensus(tree: Tree): Unit = (tree: @unchecked) match {
      case LetP(_, _, args, body) =>
        args foreach incValUseA; addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case AppC(cnt, args) =>
        incAppUseN(cnt); args foreach incValUseA
      case AppF(fun, retC, args) =>
        incAppUseA(fun); incValUseN(retC); args foreach incValUseA
      case If(_, args, thenC, elseC) =>
        args foreach incValUseA; incValUseN(thenC); incValUseN(elseC)
      case Halt(arg) =>
        incValUseA(arg)
    }

    addToCensus(tree)
    census.toMap
  }

  private def size(tree: Tree): Int = (tree: @unchecked) match {
    case LetP(_, _, _, body) => size(body) + 1
    case LetC(cs, body) => (cs map { c => size(c.body) }).sum + size(body)
    case LetF(fs, body) => (fs map { f => size(f.body) }).sum + size(body)
    case AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) | Halt(_) => 1
  }

  protected val impure: ValuePrimitive => Boolean
  protected val unstable: ValuePrimitive => Boolean

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal]
  protected val blockTag: ValuePrimitive
  protected val blockLength: ValuePrimitive

  protected val identity: ValuePrimitive

  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom]
  protected val sameArgReduceC: TestPrimitive => Boolean

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal]
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean]
}

object CPSOptimizerHigh extends CPSOptimizer(SymbolicCPSTreeModule)
    with (SymbolicCPSTreeModule.Tree => SymbolicCPSTreeModule.Tree) {
  import treeModule._
  import L3Primitive._

  def apply(tree: Tree): Tree =
    rewrite(tree)

  import scala.language.implicitConversions
  private[this] implicit def l3IntToLit(i: L3Int): Literal = IntLit(i)
  private[this] implicit def intToLit(i: Int): Literal = IntLit(L3Int(i))

  protected val impure: ValuePrimitive => Boolean = 
    Set(ByteRead, ByteWrite, BlockSet)

  protected val unstable: ValuePrimitive => Boolean = {
    case BlockAlloc(_) | BlockGet | ByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case BlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = 
    BlockTag
  protected val blockLength: ValuePrimitive = 
    BlockLength

  protected val identity: ValuePrimitive = 
    Id

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] = 
    Set((intToLit(0), IntAdd), (intToLit(1), IntMul), (intToLit(0), IntBitwiseOr), 
      (intToLit(0), IntBitwiseXOr), (intToLit(~0), IntBitwiseAnd))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] = 
    Set((IntAdd, intToLit(0)), (IntSub, intToLit(0)), (IntMul, intToLit(1)), (IntDiv, intToLit(1)), 
      (IntShiftLeft, intToLit(0)), (IntShiftRight, intToLit(0)), (IntBitwiseAnd, intToLit(~0)), 
      (IntBitwiseOr, intToLit(0)), (IntBitwiseXOr, intToLit(0)))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] = 
    Set((intToLit(0), IntMul), (intToLit(0), IntDiv), (intToLit(0), IntShiftLeft), 
      (intToLit(0), IntShiftRight), (intToLit(0), IntBitwiseAnd), (intToLit(~0), IntBitwiseOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] = 
    Set((IntMul, intToLit(0)), (IntBitwiseAnd, intToLit(0)), (IntBitwiseOr, intToLit(~0)))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (IntBitwiseAnd | IntBitwiseOr, a) => a
    case (IntSub | IntMod | IntBitwiseXOr, _) => AtomL(intToLit(0))
    case (IntDiv, _) => AtomL(intToLit(1))
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case IntLe | Eq => true
    case IntLt => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (IntAdd, Seq(IntLit(x), IntLit(y))) => x + y
    case (IntSub, Seq(IntLit(x), IntLit(y))) => x - y
    case (IntMul, Seq(IntLit(x), IntLit(y))) => x * y
    case (IntDiv, Seq(IntLit(x), IntLit(y))) if y.toInt != 0 => x / y
    case (IntMod, Seq(IntLit(x), IntLit(y))) if y.toInt != 0 => x % y

    case (IntShiftLeft,  Seq(IntLit(x), IntLit(y))) => x << y
    case (IntShiftRight, Seq(IntLit(x), IntLit(y))) => x >> y
    case (IntBitwiseAnd, Seq(IntLit(x), IntLit(y))) => x & y
    case (IntBitwiseOr,  Seq(IntLit(x), IntLit(y))) => x | y
    case (IntBitwiseXOr, Seq(IntLit(x), IntLit(y))) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {
    case (IntLt, Seq(IntLit(x), IntLit(y))) => x < y
    case (IntLe, Seq(IntLit(x), IntLit(y))) => x <= y
    case (Eq, Seq(IntLit(x), IntLit(y))) => x == y
  }
}

object CPSOptimizerLow extends CPSOptimizer(SymbolicCPSTreeModuleLow)
    with (SymbolicCPSTreeModuleLow.LetF => SymbolicCPSTreeModuleLow.LetF) {
  import treeModule._
  import CPSValuePrimitive._
  import CPSTestPrimitive._

  def apply(tree: LetF): LetF = rewrite(tree) match {
    case tree @ LetF(_, _) => tree
    case other => LetF(Seq(), other)
  }

  protected val impure: ValuePrimitive => Boolean =
    Set(BlockSet, ByteRead, ByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case BlockAlloc(_) | BlockGet | ByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case BlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = BlockTag
  protected val blockLength: ValuePrimitive = BlockLength

  protected val identity: ValuePrimitive = Id

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, Add), (1, Mul), (~0, And), (0, Or), (0, XOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((Add, 0), (Sub, 0), (Mul, 1), (Div, 1),
        (ShiftLeft, 0), (ShiftRight, 0),
        (And, ~0), (Or, 0), (XOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, Mul), (0, Div),
        (0, ShiftLeft), (0, ShiftRight),
        (0, And), (~0, Or))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((Mul, 0), (And, 0), (Or, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (And | Or, a) => a
    case (Sub | Mod | XOr, _) => AtomL(0)
    case (Div, _) => AtomL(1)
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case Le | Eq => true
    case Lt => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (Add, Seq(x, y)) => x + y
    case (Sub, Seq(x, y)) => x - y
    case (Mul, Seq(x, y)) => x * y
    case (Div, Seq(x, y)) if y.toInt != 0 => x / y
    case (Mod, Seq(x, y)) if y.toInt != 0 => x % y

    case (ShiftLeft,  Seq(x, y)) => x << y
    case (ShiftRight, Seq(x, y)) => x >> y
    case (And, Seq(x, y)) => x & y
    case (Or,  Seq(x, y)) => x | y
    case (XOr, Seq(x, y)) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {
    case (Lt, Seq(x, y)) => x < y
    case (Le, Seq(x, y)) => x <= y
    case (Eq, Seq(x, y)) => x == y
  }
}
