package l3

import l3.{ L3Primitive => L3 }
import l3.{ SymbolicCL3TreeModule => S }
import l3.{ SymbolicCPSTreeModule => C }

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  
  // Initial invocation of the transformation
  def apply(tree: S.Tree): C.Tree =
    nonTail(tree) { _ =>        
      C.Halt(C.AtomL(IntLit(L3Int(0))))  // (halt 0)
    }

  // For convenience
  val nilSeq: Seq[C.Atom] = Seq()
  
  // Utility function for atom sequences
  private def utilSeq(treeSeq: Seq[S.Tree], acc: Seq[C.Atom])(ctx: Seq[C.Atom] => C.Tree): C.Tree = {
    treeSeq match {
      case Seq() => ctx(acc.reverse)
      case Seq(head, rest @_*) => {
        nonTail(head){v: C.Atom => {utilSeq(rest, v +: acc)(ctx)}}
      }
    }
  }

  // -----------------------------------------------------------------
  // The non-tail translation
  private def nonTail(tree: S.Tree)(ctx: C.Atom => C.Tree): C.Tree = {
    implicit val pos = tree.pos
    // For convenience
    val tru = S.Lit(BooleanLit(true))(pos)
    val fals = S.Lit(BooleanLit(false))(pos)

    tree match {
      case S.Ident(name) => {
        ctx(C.AtomN(name))
      }  
      
      case S.Lit(v) => {
        ctx(C.AtomL(v))
      }

      case prim @ S.Prim(p: L3TestPrimitive, args) => {
        nonTail(S.If(prim, tru, fals))(ctx)
      }

      case S.Prim(p: L3ValuePrimitive, args) => {
        val r = Symbol.fresh("Prim_r")
        val ctxSeq = {atoms: Seq[C.Atom] => { C.LetP(r, p, atoms, ctx(C.AtomN(r))) }}
        
        utilSeq(args, nilSeq)(ctxSeq)        
      }
      
      case S.Let(seq, S.Let(rest, body)) => {
        nonTail(S.Let(seq ++ rest, body))(ctx)
      }

      case S.Let(Seq((n1, e1), restArgs @_*), e) => {
        nonTail(e1){v1: C.Atom => 
          C.LetP(n1, L3.Id, Seq(v1), nonTail(S.Let(restArgs, e))(ctx))
        }
      }

      case S.Let(Seq(), e) => {
        nonTail(e)(ctx)
      }

      case S.LetRec(funs, body) => {
        val fmap = funs.map(f => {
          val c = Symbol.fresh("LetRec_c")
          C.Fun(f.name, c, f.args, tail(f.body, c))
        })
        C.LetF(fmap, nonTail(body)(ctx))
      }

      case S.If(e1, e2, e3) => {
        val r = Symbol.fresh("If_r")
        val c = Symbol.fresh("If_c")
        val c_then = Symbol.fresh("Then_c")
        val c_else = Symbol.fresh("Else_c")

        val check = C.Cnt(c, Seq(r), ctx(C.AtomN(r)))
        val S_then = C.Cnt(c_then, Seq(), tail(e2, c))
        val S_else = C.Cnt(c_else, Seq(), tail(e3, c))

        C.LetC(Seq(check), C.LetC(Seq(S_then), C.LetC(Seq(S_else), cond(e1, c_then, c_else))))
      }

      case S.App(e, args) => {
        val c = Symbol.fresh("App_c")
        val r = Symbol.fresh("App_r")
        val S_app = C.Cnt(c, Seq(r), ctx(C.AtomN(r)))

        val ctx_app = {atoms: Seq[C.Atom] => {
          val body = nonTail(e){v: C.Atom => {
            C.AppF(v, c, atoms)
          }}

          C.LetC(Seq(S_app), body)
        }}

        utilSeq(args, nilSeq)(ctx_app)
      }

      case S.Halt(arg) => {
        nonTail(arg){v: C.Atom => C.Halt(v)}
      }
    }
  }

  // -----------------------------------------------------------------
  // The tail translation
  private def tail(tree: S.Tree, c: Symbol): C.Tree = {
    implicit val pos = tree.pos
    // For convenience
    val tru = S.Lit(BooleanLit(true))(pos)
    val fals = S.Lit(BooleanLit(false))(pos)

    tree match{
      case S.Ident(name) => {
        C.AppC(c, Seq(C.AtomN(name)))
      }

      case S.Lit(v) => {
        C.AppC(c, Seq(C.AtomL(v)))
      }

      case S.Prim(p: L3TestPrimitive, args) => 
        tail(S.If(tree, tru, fals), c)

      case S.Prim(p: L3ValuePrimitive, args) => {
        val r = Symbol.fresh("tPrim_r")
        utilSeq(args, nilSeq){atoms => 
          C.LetP(r, p, atoms, C.AppC(c, Seq(C.AtomN(r))))
        }
      }

      case S.Let(Seq(), e) => {
        tail(e, c)
      }

      case S.Let(Seq((n1, e1), restArgs @_*), e) => {
        nonTail(e1){v: C.Atom =>
          C.LetP(n1, L3.Id, Seq(v), tail(S.Let(restArgs, e), c))
        }
      }

      case S.LetRec(funs, e) => {
        val fmap = funs.map(f => {
          val c = Symbol.fresh("tLetRec_c")
          C.Fun(f.name, c, f.args, tail(f.body, c))
        })
        C.LetF(fmap, tail(e, c))
      }

      case S.If(e1, e2, e3) => {
        val c_then = Symbol.fresh("tThen_c")
        val c_else = Symbol.fresh("tElse_c")

        val S_then = C.Cnt(c_then, Seq(), tail(e2, c))
        val S_else = C.Cnt(c_else, Seq(), tail(e3, c))

        C.LetC(Seq(S_then), C.LetC(Seq(S_else), cond(e1, c_then, c_else)))
      }
      
      case S.App(e, args) => {
        utilSeq(args, nilSeq){atoms: Seq[C.Atom] =>
          nonTail(e){f => C.AppF(f, c, atoms)}
        }
      }

      case S.Halt(arg) => {
        nonTail(arg){v => C.Halt(v)}
      }
      
      case _ => nonTail(tree){v: C.Atom => C.AppC(c, Seq(v))}
    }
  }
  
  // -----------------------------------------------------------------
  // The cond translation
  private def cond(tree: S.Tree, c_then: Symbol, c_else: Symbol): C.Tree = {
    implicit val pos = tree.pos
    // For convenience
    val tru = S.Lit(BooleanLit(true))(pos)
    val fals = S.Lit(BooleanLit(false))(pos)
   
    tree match{
      case name: S.Ident => {
        cond(S.Prim(L3.Eq, Seq(name, fals)), c_else, c_then)
      }

      case S.Lit(BooleanLit(v)) =>
        C.AppC(if(v == true) c_then else c_else, Seq())

      case S.Lit(_) => 
        C.AppC(c_then, Seq())

      case prim @ S.Prim(p: L3TestPrimitive, args) => {
        utilSeq(args, nilSeq){atoms: Seq[C.Atom] =>
          C.If(p, atoms, c_then, c_else)
        }
      }

      case S.Let(Seq(), body) => {
        cond(body, c_then, c_else)
      }

      case S.Let(Seq((n1, e1), restArgs @_*), body) => {
        nonTail(e1){v1: C.Atom =>
          C.LetP(n1, L3.Id, Seq(v1), cond(S.Let(restArgs, body), c_then, c_else))
        }
      }
      
      case S.If(e1, S.Lit(BooleanLit(v1)), S.Lit(BooleanLit(v2))) => { 
        if(v1 == false) cond(e1, c_else, c_then)
        else cond(e1, c_then, c_else)
      }
      
      case S.If(e1, e2, S.Lit(BooleanLit(v3))) => {
        val c = Symbol.fresh("cond_c")
        val (c_then_, c_else_) = if(!v3) (c_then, c_else) else (c_else, c_then)
        val cond_S = C.Cnt(c, Seq(), cond(e2, c_then_, c_else_))
        C.LetC(Seq(cond_S), cond(e1, c, c_else_))
      }

      case S.If(e1, e2 @ S.Lit(BooleanLit(_)), e3) => {
        cond(S.If(e1, e3, e2), c_else, c_then)
      }
      
      case S.If(e1, e2, e3) => {
        nonTail(e1){v: C.Atom => 
          C.If(L3.Eq, Seq(v, C.AtomL(BooleanLit(false))), c_else, c_then)
        }
      }

      case other => {
        nonTail(other){v: C.Atom  => 
          C.If(L3.Eq, Seq(v, C.AtomL(BooleanLit(true))), c_then, c_else)
        }
      }  
    }
  }
}
