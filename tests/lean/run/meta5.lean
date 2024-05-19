import Lean.Meta

open Lean
open Lean.Meta

def tst1 : MetaM Unit :=
withLocalDeclD `y (mkConst `Nat) $ fun y => do
withLetDecl `x (mkConst `Nat) (mkNatLit 0) $ fun x => do {
  let mvar ← mkFreshExprMVar (mkConst `Nat) MetavarKind.syntheticOpaque;
  trace[Meta.debug] mvar;
  let r ← mkLambdaFVars #[y, x] mvar;
  trace[Message.debug] r;
  let v := mkApp2 (mkConst `Nat.add) x y;
  assignExprMVar mvar.mvarId! v;
  trace[Meta.debug] mvar;
  trace[Meta.debug] r;
  let mctx ← getMCtx;
  mctx.decls.forM fun mvarId mvarDecl => do
    trace[Meta.debug] m!"?{mvarId.name} : {mvarDecl.type}"
}

set_option trace.Meta.debug true

/--
info: [Meta.debug] ?m.3
[Meta.debug] x.add y
[Meta.debug] fun y =>
      let x := 0;
      x.add y
[Meta.debug] ?_uniq.4 : Nat →
      Nat →
        let x := 0;
        Nat
[Meta.debug] ?_uniq.3 : Nat
-/
#guard_msgs in
#eval tst1
