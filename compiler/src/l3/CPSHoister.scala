package l3

import SymbolicCPSTreeModuleLow._

object CPSHoister extends (Tree => LetF) {
  def apply(tree: Tree): LetF = {
    // Helpers for continuations and functions
    def hoist_cnts(cnt: Cnt): (Cnt, Seq[Fun]) = {
      val (e, fs) = hoist(cnt.body, Seq())
      return (Cnt(cnt.name, cnt.args, e), fs)
    }
    def hoist_funs(fun: Fun): (Seq[Fun]) = {
      val (e, fs) = hoist(fun.body, Seq())
      val seq_new = Seq(Fun(fun.name, fun.retC, fun.args, e))
      return (seq_new ++ fs)
    }

    // Hoisting - collect all lets
    def hoist(sub_tree: Tree, funs: Seq[Fun]): (Tree, Seq[Fun]) = {
      sub_tree match {
        case LetP(n, p, args, body) => {
          val (e, fs) = hoist(body, funs)
          return (LetP(n, p, args, e), fs)
        }
        case LetC(cnts, body) => {
          val (e, fs) = hoist(body, funs)
          val (cnts1, fs1) = cnts.map(hoist_cnts).unzip
          val fs_new = fs1.flatten ++ fs
          return (LetC(cnts1, e), fs_new)
        }
        case LetF(funs, body) => {
          val (e, fs) = hoist(body, Seq())
          val fs_new = funs.flatMap(hoist_funs) ++ fs
          return (e, fs_new)
        }
        case other => return (other, Seq())
      }
    }

    // Return the single hoisted LetF
    val (sub_tree, fs) = hoist(tree, Seq())
    return LetF(fs, sub_tree)    
  }
}
