/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Elab.Term

namespace Lean
namespace Elab
namespace Term

@[builtinTermElab dollar] def elabDollar : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `($f $ $a) => `($f $a)
| _          => unreachable!

@[builtinTermElab dollarProj] def elabDollarProj : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `($term $.$field) => `($(term).$field)
| _                 => unreachable!

@[builtinTermElab «if»] def elabIf : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `(if $h : $cond then $t else $e) => let h := mkTermIdFromIdent h; `(dite $cond (fun $h => $t) (fun $h => $e))
| `(if $cond then $t else $e)      => `(ite $cond $t $e)
| _                                => unreachable!

@[builtinTermElab subtype] def elabSubtype : TermElab :=
adaptExpander $ fun stx => match_syntax stx with
| `({ $x : $type // $p }) => let x := mkTermIdFromIdent x; `(Subtype (fun ($x : $type) => $p))
| `({ $x // $p })         => let x := mkTermIdFromIdent x; `(Subtype (fun ($x : _) => $p))
| _                       => unreachable!

@[builtinTermElab anonymousCtor] def elabAnoymousCtor : TermElab :=
fun stx expectedType? => do
let ref := stx.val;
tryPostponeIfNoneOrMVar expectedType?;
match expectedType? with
| none              => throwError ref "invalid constructor ⟨...⟩, expected type must be known"
| some expectedType => do
  expectedType ← instantiateMVars ref expectedType;
  let expectedType := expectedType.consumeMData;
  match expectedType.getAppFn with
  | Expr.const constName _ _ => do
    env ← getEnv;
    match env.find? constName with
    | some (ConstantInfo.inductInfo val) =>
      if val.ctors.length != 1 then
        throwError ref ("invalid constructor ⟨...⟩, '" ++ constName ++ "' must have only one constructor")
      else
        let ctor := mkTermId ref val.ctors.head!;
        let args := (stx.getArg 1).getArgs.getEvenElems; do
        withMacroExpansion ref $ elabTerm (mkAppStx ctor args) expectedType?
    | _ => throwError ref ("invalid constructor ⟨...⟩, '" ++ constName ++ "' is not an inductive type")
  | _ => throwError ref ("invalid constructor ⟨...⟩, expected type is not an inductive type " ++ indentExpr expectedType)

def elabInfix (f : Syntax) : TermElab :=
fun stx expectedType? => do
  -- term `op` term
  let a := stx.getArg 0;
  let b := stx.getArg 2;
  elabTerm (mkAppStx f #[a, b]) expectedType?

def elabInfixOp (op : Name) : TermElab :=
fun stx expectedType? => elabInfix (mkTermId (stx.getArg 1) op) stx expectedType?

@[builtinTermElab prod] def elabProd : TermElab := elabInfixOp `Prod
@[builtinTermElab fcomp] def ElabFComp : TermElab := elabInfixOp `Function.comp

@[builtinTermElab add] def elabAdd : TermElab := elabInfixOp `HasAdd.add
@[builtinTermElab sub] def elabSub : TermElab := elabInfixOp `HasSub.sub
@[builtinTermElab mul] def elabMul : TermElab := elabInfixOp `HasMul.mul
@[builtinTermElab div] def elabDiv : TermElab := elabInfixOp `HasDiv.div
@[builtinTermElab mod] def elabMod : TermElab := elabInfixOp `HasMod.mod
@[builtinTermElab modN] def elabModN : TermElab := elabInfixOp `HasModN.modn
@[builtinTermElab pow] def elabPow : TermElab := elabInfixOp `HasPow.pow

@[builtinTermElab le] def elabLE : TermElab := elabInfixOp `HasLessEq.LessEq
@[builtinTermElab ge] def elabGE : TermElab := elabInfixOp `GreaterEq
@[builtinTermElab lt] def elabLT : TermElab := elabInfixOp `HasLess.Less
@[builtinTermElab gt] def elabGT : TermElab := elabInfixOp `Greater
@[builtinTermElab eq] def elabEq : TermElab := elabInfixOp `Eq
@[builtinTermElab ne] def elabNe : TermElab := elabInfixOp `Ne
@[builtinTermElab beq] def elabBEq : TermElab := elabInfixOp `HasBeq.beq
@[builtinTermElab bne] def elabBNe : TermElab := elabInfixOp `bne
@[builtinTermElab heq] def elabHEq : TermElab := elabInfixOp `HEq
@[builtinTermElab equiv] def elabEquiv : TermElab := elabInfixOp `HasEquiv.Equiv

@[builtinTermElab and] def elabAnd : TermElab := elabInfixOp `And
@[builtinTermElab or] def elabOr : TermElab := elabInfixOp `Or
@[builtinTermElab iff] def elabIff : TermElab := elabInfixOp `Iff

@[builtinTermElab band] def elabBAnd : TermElab := elabInfixOp `and
@[builtinTermElab bor] def elabBOr : TermElab := elabInfixOp `or

@[builtinTermElab append] def elabAppend : TermElab := elabInfixOp `HasAppend.append
@[builtinTermElab cons] def elabCons : TermElab := elabInfixOp `List.cons

@[builtinTermElab andthen] def elabAndThen : TermElab := elabInfixOp `HasAndthen.andthen
@[builtinTermElab bindOp] def elabBind : TermElab := elabInfixOp `HasBind.bind

@[builtinTermElab seq] def elabseq : TermElab := elabInfixOp `HasSeq.seq
@[builtinTermElab seqLeft] def elabseqLeft : TermElab := elabInfixOp `HasSeqLeft.seqLeft
@[builtinTermElab seqRight] def elabseqRight : TermElab := elabInfixOp `HasSeqRight.seqRight

@[builtinTermElab map] def elabMap : TermElab := elabInfixOp `Functor.map
@[builtinTermElab mapRev] def elabMapRev : TermElab := elabInfixOp `Functor.mapRev
@[builtinTermElab mapConst] def elabMapConst : TermElab := elabInfixOp `Functor.mapConst
@[builtinTermElab mapConstRev] def elabMapConstRev : TermElab := elabInfixOp `Functor.mapConstRev

@[builtinTermElab orelse] def elabOrElse : TermElab := elabInfixOp `HasOrelse.orelse
@[builtinTermElab orM] def elabOrM : TermElab := elabInfixOp `orM
@[builtinTermElab andM] def elabAndM : TermElab := elabInfixOp `andM

/-
TODO
@[builtinTermElab] def elabsubst : TermElab := elabInfixOp infixR " ▸ " 75
-/

end Term
end Elab
end Lean
