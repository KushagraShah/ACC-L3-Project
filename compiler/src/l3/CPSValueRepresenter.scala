package l3

import l3.{ L3Primitive => L3 }
import l3.{ CPSValuePrimitive => CPS }
import l3.{ CPSTestPrimitive => CPST }
import l3.{ SymbolicCPSTreeModule => H }
import l3.{ SymbolicCPSTreeModuleLow => L}

object CPSValueRepresenter extends (H.Tree => L.Tree) {
	
	// ============ Helper Functions ============ //	
	// Quick variable for 'unboxed 1'
	val unbox1 = L.AtomL(1) 

	// Fresh symbol and LetP call for any primitive
	def fresh_LetP(prim: L.ValuePrimitive, args: Seq[L.Atom])(ctx: L.AtomN => L.Tree): L.Tree = {
		val f = Symbol.fresh("fx")
		L.LetP(f, prim, args, ctx(L.AtomN(f))) 
	}
	// Quick subtract '1'
	def subtract1(atom: L.Atom)(body: L.Atom => L.Tree): L.Tree = {
		fresh_LetP(CPS.Sub, Seq(atom, unbox1))(body)
	}
	// Quick shift left by '1'
	def shiftleft1(atom: L.Atom)(body: L.Atom => L.Tree): L.Tree = {
		fresh_LetP(CPS.ShiftLeft, Seq(atom, unbox1))(body)
	}
	// Helper for unboxing
	def unboxInt(atom: H.Atom)(ctx: L.Atom => L.Tree): L.Tree = {
		val f = Symbol.fresh("fInt")
		L.LetP(f, CPS.ShiftRight, Seq(rewrite(atom), unbox1), ctx(L.AtomN(f)))
	}
	// Helper for boxing
	def boxInt(atom: L.Atom, name: H.Name = Symbol.fresh("fname"))(ctx: L.Atom => L.Tree): L.Tree = {
		shiftleft1(atom){fx =>
			L.LetP(name, CPS.Add, Seq(fx, unbox1), ctx(L.AtomN(name)))
		}	
	}

	// ============ Closure Conversion Helpers ============ //
	
	// Helper function for substitutions
	def substitute(tree: L.Tree)(implicit s: Subst[Symbol]): L.Tree = {
		def substT(tree: L.Tree): L.Tree = tree match {
			case L.LetP(n, p, v, e) => L.LetP(n, p, v.map{a => substA(a)}, substT(e))
			case L.LetC(cnts, e) => L.LetC(cnts.map(substC), substT(e))
			case L.LetF(funs, e) => L.LetF(funs.map(substF), substT(e))
			case L.AppC(c, atoms) => L.AppC(c, atoms.map{a => substA(a)})
			case L.AppF(v, c, vals) => L.AppF(substA(v), c, vals.map(substA))
			case L.If(p, v, ct, cf) => L.If(p, v.map(substA), ct, cf)
			case L.Halt(atom) => L.Halt(substA(atom))
		}
		def substC(cnt: L.Cnt): L.Cnt = cnt match {
			case L.Cnt(name, args, e) => L.Cnt(name, args, substT(e))
		}
		def substF(fun: L.Fun): L.Fun = fun match {
			case L.Fun(name, retC, args, e) => L.Fun(name, retC, args, substT(e))
		}
		def substA(atom: L.Atom): L.Atom = atom match {
			case L.AtomL(_) => atom
			case L.AtomN(n) => L.AtomN(s.getOrElse(n,n))
		}
		
		substT(tree)		
	}

	// Compute the set of free variables
	def atom2FV(atom: H.Atom): Set[Symbol] = atom match {
		case H.AtomN(name) => Set(name)
		case _ => Set()
	}
	def prim2FV(tree: H.Tree): Set[Symbol] = tree match {
		case H.LetP(n, p, v, e) => {
			prim2FV(e) ++ v.flatMap(atom2FV) - n
		}
		case H.LetC(cnts, e) => {
			prim2FV(e) ++ cnts.flatMap{
				case H.Cnt(_, args, body) => prim2FV(body) -- args.toSet
			}
		}
		case H.LetF(funs, e) => {
			val f_FV = funs.flatMap{
				case H.Fun(name, _, args, body) => prim2FV(body) -- args.toSet
			}
			prim2FV(e) ++ f_FV -- funs.map(_.name).toSet
		}
		case H.AppC(_, atoms) => {
			atoms.flatMap(atom2FV).toSet
		}
		case H.AppF(v, c, vals) => {
			atom2FV(v) ++ vals.flatMap(atom2FV).toSet
		}
		case H.If(_, v, _, _) => {
			v.flatMap(atom2FV).toSet
		}
		case H.Halt(atom) => {
			atom2FV(atom)
		}		
	}
	def fun2FV(fun: H.Fun): Set[Symbol] = {
		prim2FV(fun.body) -- Set(fun.name) -- fun.args.toSet
	}

	// ============ Closure Conversion ============ //
	// One huge function with nested helper functions
	def closure(h_letf: H.LetF): L.Tree = {
		
		// ----- Mini-Helper Functions ----- // 
		// Helpers for BlockGet and BlockSet
		def blockget_help(fun: Symbol, env: Symbol, fv: Seq[(Symbol, Int)], ctx: Subst[Symbol], body: L.Tree): 
			(L.Tree, Subst[Symbol]) = {
			fv match {
				case Seq((symbol, index), tail @ _*) => {
					val v = Symbol.fresh("v_bg")
					val (body_l, ctx_l) = blockget_help(fun, env, tail, ctx+(symbol->v), body)
					val letp = L.LetP(v, CPS.BlockGet, Seq(L.AtomN(env), L.AtomL(index)), substitute(body_l)(ctx_l))
					(letp, ctx_l)
				}
				case Seq() => {
					(substitute(body)(ctx), ctx)
				}
			}
		}
		def blockset_help(fun: Symbol, fv: Seq[(Symbol, Int)], body: L.Tree): L.Tree = {
			fv match {
				case Seq((symbol, index), tail @ _*) => {
					fresh_LetP(CPS.BlockSet, Seq(L.AtomN(fun), L.AtomL(index), L.AtomN(symbol))){_ =>
						blockset_help(fun, fv.tail, body)
					}
				}
				case Seq() => body
			}
		}
		
		// ----- Main closure steps ----- //
		// Close functions; Allocate and initialize closure blocks
		def close_fun(fun: H.Fun): (L.Fun, (Symbol, Seq[Symbol]), Symbol) = {
			val env = Symbol.fresh("env")
			val w = Symbol.fresh("worker")

			val fun_fv = fun2FV(fun).toSeq
			val fun_zip = fun_fv.zip(1 to fun_fv.size)
			val (body, ctx) = blockget_help(fun.name, env, fun_zip, Map(fun.name->env), apply(fun.body))
			
			val fun_set = Set(fun.name) ++ fun.args.toSet
			val filtered_args = ctx.filter{
				case (free_, new_) => !fun_set.contains(free_)
			}

			val closed_fun = L.Fun(w, fun.retC, Seq(env) ++ fun.args, body)
			(closed_fun, (fun.name, filtered_args.keys.toSeq), w)
		}
		def alloc_closure(traits: Seq[(Symbol, Int)], body: L.Tree): L.Tree = traits match {
			case Seq() => body
			case Seq((name, size), others @ _*) => {
				L.LetP(name, CPS.BlockAlloc(202), Seq(L.AtomL(size)), alloc_closure(others, body))
			}
		}
		def init_closure(ctxs: Seq[(Symbol, Seq[Symbol])], body: H.Tree, ws: Seq[Symbol]): L.Tree = {
			// Helper function for recursive closures
			def init_help(ctxs: Seq[(Symbol, Seq[Symbol])], body: H.Tree) : L.Tree = ctxs match {
				case Seq((fun, fun_fvs), other_fvs @_*) => {
					blockset_help(fun, fun_fvs.zip(1 to fun_fvs.length), init_closure(other_fvs, body, ws.tail))
				}
				case Seq() => apply(body)
			}
			// Initialize for function and its free variables
			ctxs match {
				case Seq(head, tail @ _*) => {
					val (fun, fun_fvs) = ctxs.head
					fresh_LetP(CPS.BlockSet, Seq(L.AtomN(fun), L.AtomL(0), L.AtomN(ws.head))){_ => 
						init_help(ctxs, body)
					}
				}
				case Seq() => apply(body)
			}
		}

		// ----- Instantiate above functions ----- //
		val (closed_funs, ctxs, ws) = h_letf.funs.map(close_fun).unzip3
		val traits = ctxs.map{
			case(name, fvs) => (name, fvs.size + 1)
		}

		L.LetF(closed_funs, alloc_closure(traits, init_closure(ctxs, h_letf.body, ws)))
	}

	// ============ Transform Atoms ============ //
	private def rewrite(atom: H.Atom): L.Atom = atom match{
		case H.AtomN(name) => {
			L.AtomN(name)
		}
		case H.AtomL(IntLit(value)) => {
			L.AtomL((value.toInt << 1) | 1)
		}
		case H.AtomL(CharLit(char)) => {
			L.AtomL((char << 3) | 6)
		}
		case H.AtomL(BooleanLit(bit)) => {
			L.AtomL(if(bit) 0x1A else 0xA)
		}
		case H.AtomL(UnitLit) => {
			L.AtomL(2)
		} 
	}	

	// ============ Transform Primitives ============ //
	// Huge pattern match
	def apply(tree: H.Tree): L.Tree = tree match{
		
		// ----- Continuations ----- //
		// No need for translation
		
		case H.LetC(cnts, e) => {
			L.LetC(cnts.map{
				case H.Cnt(ni, ai, ei) => L.Cnt(ni, ai, apply(ei))
			}, apply(e))
		}

		case H.AppC(cnt_name, v_bindings) => {
			L.AppC(cnt_name, v_bindings.map(rewrite))
		}
		
		// ----- Functions ----- //
		// Use correct method: closure conversion

		case h_letf @ H.LetF(funs, body) => {
			closure(h_letf)
		}

		case H.AppF(fun, retC, args) => {
			val f = Symbol.fresh("f_cc")
			val re_args = Seq(rewrite(fun)) ++ args.map(rewrite)
			L.LetP(f, CPS.BlockGet, Seq(rewrite(fun), L.AtomL(0)), 
				L.AppF(L.AtomN(f), retC, re_args))
		}

		// ----- Primitives on blocks ----- //
		// BlockP, Alloc, Tag, Length, Get, Set
		
		case H.If(L3.BlockP, Seq(v), c_then, c_else) => {
			fresh_LetP(CPS.And, Seq(rewrite(v), L.AtomL(3))){fx =>
				L.If(CPST.Eq, Seq(fx, L.AtomL(0)), c_then, c_else)
			}
		}

		case H.LetP(name, L3.BlockAlloc(tag), Seq(v), body) => {
			unboxInt(v){fx =>
				L.LetP(name, CPS.BlockAlloc(tag), Seq(fx), apply(body))
			}
		}

		case H.LetP(name, L3.BlockTag, Seq(v), body) => {
			fresh_LetP(CPS.BlockTag, Seq(rewrite(v))){res =>
				boxInt(res, name){_ => apply(body)}
			}
		}

		case H.LetP(name, L3.BlockLength, Seq(v), body) => {
			fresh_LetP(CPS.BlockLength, Seq(rewrite(v))){t1 =>
				shiftleft1(t1){t2 =>
					L.LetP(name, CPS.Add, Seq(t2, unbox1), apply(body))
				}
			}
		}

		case H.LetP(name, L3.BlockGet, Seq(block, slot), body) => {
			unboxInt(slot){fx =>
				L.LetP(name, CPS.BlockGet, Seq(rewrite(block), fx), apply(body))
			}
		}

		case H.LetP(name, L3.BlockSet, Seq(v1, v2, v3), body) => {
			unboxInt(v2){fx => 
				L.LetP(name, CPS.BlockSet, Seq(rewrite(v1), fx, rewrite(v3)), apply(body))
			}
		}

		// ----- Primitives on integers ----- //
		// IntP, Add, Sub, Mul, Div, Mod

		case H.If(L3.IntP, Seq(v), c_then, c_else) => {
			val x = Symbol.fresh("intp_x")
			L.LetP(x, CPS.And, Seq(unbox1, rewrite(v)),
				L.If(CPST.Eq, Seq(L.AtomN(x), unbox1), c_then, c_else))
		}

		case H.LetP(name, L3.IntAdd, atoms @ Seq(_, _), body) => {
			fresh_LetP(CPS.Add, atoms.map(rewrite)){fx => 
				L.LetP(name, CPS.Sub, Seq(fx, unbox1), apply(body))
			}
		}

		case H.LetP(name, L3.IntSub, atoms @ Seq(_, _), body) => {
			fresh_LetP(CPS.Sub, atoms.map(rewrite)){fx => 
				L.LetP(name, CPS.Add, Seq(fx, unbox1), apply(body))
			}
		}

		case H.LetP(name, L3.IntMul, atoms @ Seq(v1, v2), body) => {
			fresh_LetP(CPS.Sub, Seq(rewrite(v1), unbox1)){t1 =>
				unboxInt(v2){t2 =>
					fresh_LetP(CPS.Mul, Seq(t1, t2)){fx =>
						L.LetP(name, CPS.Add, Seq(fx, unbox1), apply(body))
					}
				}
			}
		}

		case H.LetP(name, L3.IntDiv, atoms @ Seq(v1, v2), body) => {
			subtract1(rewrite(v1)){t1: L.Atom =>
				subtract1(rewrite(v2)){t2: L.Atom =>
					fresh_LetP(CPS.Div, Seq(t1, t2)){res =>
						boxInt(res, name){_ => apply(body)}
					}
				}
			}
		}

		case H.LetP(name, L3.IntMod, atoms @ Seq(v1, v2), body) => {
			unboxInt(v1){t1 =>
				unboxInt(v2){t2 =>
					fresh_LetP(CPS.Mod, Seq(t1, t2)){res =>
						boxInt(res, name){_ => apply(body)}
					}
				}
			}
		}

		// ShiftLeft, ShiftRight, And, Or, XOr

		case H.LetP(name, L3.IntShiftLeft, atoms @ Seq(v1, v2), body) => {
			subtract1(rewrite(v1)){t1 =>
				unboxInt(v2){t2 =>
					fresh_LetP(CPS.ShiftLeft, Seq(t1, t2)){res =>
						L.LetP(name, CPS.Add, Seq(res, unbox1), apply(body))
					}
				}
			}
		}

		case H.LetP(name, L3.IntShiftRight, atoms @ Seq(v1, v2), body) => {
			unboxInt(v1){t1 =>
				unboxInt(v2){t2 =>
					fresh_LetP(CPS.ShiftRight, Seq(t1, t2)){res =>
						boxInt(res, name){_ => apply(body)}
					}
				}
			}
		}

		case H.LetP(name, L3.IntBitwiseAnd, atoms @ Seq(_, _), body) => {
			L.LetP(name, CPS.And, atoms.map(rewrite), apply(body))
		}

		case H.LetP(name, L3.IntBitwiseOr, atoms @ Seq(_, _), body) => {
			L.LetP(name, CPS.Or, atoms.map(rewrite), apply(body))
		}

		case H.LetP(name, L3.IntBitwiseXOr, atoms @ Seq(_, _), body) => {
			fresh_LetP(CPS.XOr, atoms.map(rewrite)){fx =>
				L.LetP(name, CPS.Or, Seq(fx, unbox1), apply(body))
			}
		}

		// IntLt, IntLe, ByteRead, ByteWrite, IntToChar

		case H.If(L3.IntLt, atoms @ Seq(_, _), c_then, c_else) => {
			L.If(CPST.Lt, atoms.map(rewrite), c_then, c_else)
		}
		
		case H.If(L3.IntLe, atoms @ Seq(_, _), c_then, c_else) => {
			L.If(CPST.Le, atoms.map(rewrite), c_then, c_else)
		}

		case H.LetP(name, L3.ByteRead, Seq(), body) => {
			fresh_LetP(CPS.ByteRead, Seq()){res => 
				boxInt(res, name){_ => apply(body)}
			}
		}

		case H.LetP(name, L3.ByteWrite, Seq(v), body) => {
			unboxInt(v){n => 
				L.LetP(name, CPS.ByteWrite, Seq(n), apply(body))
			}
		}

		case H.LetP(name, L3.IntToChar, Seq(v), e) => {
			fresh_LetP(CPS.ShiftLeft, Seq(rewrite(v), L.AtomL(2))){fx =>
				L.LetP(name, CPS.Add, Seq(fx, L.AtomL(2)), apply(e))
			}
		}

		// ----- Primitives on characters ----- //
		// CharP, CharToInt

		case H.If(L3.CharP, Seq(v), c_then, c_else) => {
			fresh_LetP(CPS.And, Seq(rewrite(v), L.AtomL(7))){fx => 
				L.If(CPST.Eq, Seq(fx, L.AtomL(6)), c_then, c_else)
			}
		}

		case H.LetP(name, L3.CharToInt, Seq(v), e) => {
			L.LetP(name, CPS.ShiftRight, Seq(rewrite(v), L.AtomL(2)), apply(e))
		}


		// ----- Primitives on booleans ----- //
		// BoolP
		case H.If(L3.BoolP, Seq(v), c_then, c_else) => {
			val x = Symbol.fresh("boolp_x")
			L.LetP(x, CPS.And, Seq(rewrite(v), L.AtomL(0xF)),
				L.If(CPST.Eq, Seq(L.AtomN(x), L.AtomL(0xA)), c_then, c_else))
		}
		
		// ----- Primitives on unit ----- //
		// UnitP
		case H.If(L3.UnitP, Seq(v), c_then, c_else) => {
			L.If(CPST.Eq, Seq(rewrite(v), L.AtomL(2)), c_then, c_else)
		}

		// ----- Primitives on arbitrary values ----- //
		// Eq, Id, Halt

		case H.If(L3.Eq, atoms @ Seq(_, _), c_then, c_else) => {
			L.If(CPST.Eq, atoms.map(rewrite), c_then, c_else)
		}

		case H.LetP(name, L3.Id, Seq(v), body) => {
			L.LetP(name, CPS.Id, Seq(rewrite(v)), apply(body))
		}

		case H.Halt(atom) => {
			unboxInt(atom){s => L.Halt(s)}
		}

		// ----- Failsafe in case of missing translations ----- //
		case other => throw new Exception(s"Error: $other translation missing")
		
	}
	// end of match-case
}
