// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Internalize
// Imports: Init.Grind.Util Init.Grind.Lemmas Lean.Meta.LitValues Lean.Meta.Match.MatcherInfo Lean.Meta.Match.MatchEqsExt Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Canon Lean.Meta.Tactic.Grind.Beta Lean.Meta.Tactic.Grind.MatchCond Lean.Meta.Tactic.Grind.Arith.Internalize
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_internalize___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_internalize___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__3;
extern lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare;
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1;
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_internalize___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__6;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__2;
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isDIte(lean_object*);
lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Offset_0__Lean_Meta_Grind_Arith_Offset_setUnsat___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__1;
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___closed__4;
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_addCongrTable___spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_activateTheorem___closed__1;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_propagateBetaForNewApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at_Lean_Meta_Grind_addCongrTable___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isCongruent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_internalize___lambda__2___closed__7;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4;
static lean_object* l_Lean_Meta_Grind_internalize___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__3;
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_activateTheorem___closed__2;
uint64_t l_Lean_Meta_Grind_congrHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_normalizeLevels___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__4;
lean_object* l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__1;
lean_object* l_Lean_Meta_Grind_Arith_Offset_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_setENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at_Lean_Meta_Grind_addCongrTable___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_internalize___lambda__2___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_internalize___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_internalize___lambda__3___closed__1;
uint8_t l_Lean_Meta_Grind_EMatchTheorems_isErased(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__1;
static lean_object* l_Lean_Meta_Grind_internalize___lambda__2___closed__3;
lean_object* l_Lean_Meta_Grind_propagateUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getENode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__4;
lean_object* l_Lean_Meta_Grind_EMatchTheorems_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__2;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_mkENode_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_internalize___lambda__2___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at_Lean_addAliasEntry___spec__16(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Meta_Grind_unfoldReducible___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__1(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_addCongrTable___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_groundPattern_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__2;
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_EMatchTheorems_insert___spec__9(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_Meta_Grind_internalize___lambda__2___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__4;
lean_object* l_Lean_Meta_reduceMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_activateTheorem___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_addCongrTable___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2(lean_object*, lean_object*, size_t, lean_object*);
static size_t l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__2;
static lean_object* l_Lean_Meta_Grind_activateTheorem___closed__4;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_internalize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__11;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_addCongrTable___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__6;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
uint8_t l_Lean_Expr_isIte(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__2(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchEqTheorem(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_activateTheorem___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2;
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkGroundPattern(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at_Lean_Meta_Grind_addCongrTable___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__4;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_internalize___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__5;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__3;
lean_object* l_Lean_Meta_Grind_registerParent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_Grind_activateTheorem___closed__3;
lean_object* l_Lean_PersistentHashMap_erase___at_Lean_Meta_Grind_EMatchTheorems_retrieve_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1;
static lean_object* l_Lean_Meta_Grind_internalize___lambda__2___closed__6;
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMorallyIff___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_internalize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_object* l_Lean_Meta_Grind_mkENodeCore(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_internalize___lambda__2___closed__5;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__2(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__3;
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_mkENode_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_internalize___spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___boxed(lean_object**);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_Grind_addCongrTable___closed__2;
static lean_object* l_Lean_Meta_Grind_internalize___lambda__3___closed__2;
lean_object* l_Lean_Meta_Grind_Origin_key(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMorallyIff(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_congrPlaceholderProof;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_HeadIndex_hash(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__2;
static lean_object* l_Lean_Meta_Grind_addCongrTable___closed__3;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__3;
static lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__8;
lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Grind_activateTheorem___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_internalize___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_internalize___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at_Lean_Meta_Grind_addCongrTable___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_fget(x_2, x_5);
lean_inc(x_11);
lean_inc(x_6);
x_12 = l_Lean_Meta_Grind_isCongruent(x_7, x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
static size_t _init_l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = 5;
x_9 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
x_10 = lean_usize_land(x_3, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_box(2);
x_13 = lean_array_get(x_12, x_6, x_11);
lean_dec(x_11);
lean_dec(x_6);
switch (lean_obj_tag(x_13)) {
case 0:
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_17 = l_Lean_Meta_Grind_isCongruent(x_7, x_4, x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_2);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
lean_inc(x_19);
x_21 = l_Lean_Meta_Grind_isCongruent(x_7, x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_19);
lean_free_object(x_2);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_23);
return x_2;
}
}
}
case 1:
{
lean_object* x_24; size_t x_25; 
lean_dec(x_7);
lean_free_object(x_2);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_usize_shift_right(x_3, x_8);
x_2 = x_24;
x_3 = x_25;
goto _start;
}
default: 
{
lean_object* x_27; 
lean_dec(x_7);
lean_free_object(x_2);
lean_dec(x_4);
lean_dec(x_1);
x_27 = lean_box(0);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
x_30 = 5;
x_31 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
x_32 = lean_usize_land(x_3, x_31);
x_33 = lean_usize_to_nat(x_32);
x_34 = lean_box(2);
x_35 = lean_array_get(x_34, x_28, x_33);
lean_dec(x_33);
lean_dec(x_28);
switch (lean_obj_tag(x_35)) {
case 0:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_1);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
lean_inc(x_36);
x_39 = l_Lean_Meta_Grind_isCongruent(x_29, x_4, x_36);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
x_40 = lean_box(0);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
case 1:
{
lean_object* x_43; size_t x_44; 
lean_dec(x_29);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = lean_usize_shift_right(x_3, x_30);
x_2 = x_43;
x_3 = x_44;
goto _start;
}
default: 
{
lean_object* x_46; 
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_1);
x_46 = lean_box(0);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_dec(x_2);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Lean_PersistentHashMap_findEntryAtAux___at_Lean_Meta_Grind_addCongrTable___spec__3(x_1, x_47, x_48, lean_box(0), x_49, x_4);
lean_dec(x_48);
lean_dec(x_47);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___at_Lean_Meta_Grind_addCongrTable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_Meta_Grind_congrHash(x_4, x_3);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2(x_1, x_2, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_addCongrTable___spec__6(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_6, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_array_fget(x_3, x_6);
x_12 = lean_array_fget(x_4, x_6);
lean_inc(x_11);
x_13 = l_Lean_Meta_Grind_congrHash(x_8, x_11);
x_14 = lean_uint64_to_usize(x_13);
x_15 = 1;
x_16 = lean_usize_sub(x_2, x_15);
x_17 = 5;
x_18 = lean_usize_mul(x_17, x_16);
x_19 = lean_usize_shift_right(x_14, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_6, x_20);
lean_dec(x_6);
lean_inc(x_1);
x_22 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(x_1, x_7, x_19, x_2, x_11, x_12);
x_5 = lean_box(0);
x_6 = x_21;
x_7 = x_22;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_addCongrTable___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_array_get_size(x_6);
x_10 = lean_nat_dec_lt(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
x_14 = lean_array_push(x_6, x_4);
x_15 = lean_array_push(x_7, x_5);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_16 = lean_array_push(x_6, x_4);
x_17 = lean_array_push(x_7, x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_array_fget(x_6, x_3);
lean_inc(x_4);
x_20 = l_Lean_Meta_Grind_isCongruent(x_8, x_4, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
x_3 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_2, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_27 = lean_array_fset(x_6, x_3, x_4);
x_28 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
lean_ctor_set(x_2, 1, x_28);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_29 = lean_array_fset(x_6, x_3, x_4);
x_30 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = 1;
x_11 = 5;
x_12 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
x_13 = lean_usize_land(x_3, x_12);
x_14 = lean_usize_to_nat(x_13);
x_15 = lean_array_get_size(x_8);
x_16 = lean_nat_dec_lt(x_14, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_fget(x_8, x_14);
x_18 = lean_box(0);
x_19 = lean_array_fset(x_8, x_14, x_18);
switch (lean_obj_tag(x_17)) {
case 0:
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_5);
x_23 = l_Lean_Meta_Grind_isCongruent(x_9, x_5, x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_17);
x_24 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_21, x_22, x_5, x_6);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_array_fset(x_19, x_14, x_25);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
else
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_21);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 0, x_5);
x_27 = lean_array_fset(x_19, x_14, x_17);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
lean_inc(x_28);
lean_inc(x_5);
x_30 = l_Lean_Meta_Grind_isCongruent(x_9, x_5, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_28, x_29, x_5, x_6);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_array_fset(x_19, x_14, x_32);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_33);
return x_2;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_29);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_6);
x_35 = lean_array_fset(x_19, x_14, x_34);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_35);
return x_2;
}
}
}
case 1:
{
uint8_t x_36; 
lean_dec(x_9);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_usize_shift_right(x_3, x_11);
x_39 = lean_usize_add(x_4, x_10);
x_40 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(x_1, x_37, x_38, x_39, x_5, x_6);
lean_ctor_set(x_17, 0, x_40);
x_41 = lean_array_fset(x_19, x_14, x_17);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_41);
return x_2;
}
else
{
lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
lean_dec(x_17);
x_43 = lean_usize_shift_right(x_3, x_11);
x_44 = lean_usize_add(x_4, x_10);
x_45 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(x_1, x_42, x_43, x_44, x_5, x_6);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_array_fset(x_19, x_14, x_46);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_47);
return x_2;
}
}
default: 
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_9);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_6);
x_49 = lean_array_fset(x_19, x_14, x_48);
lean_dec(x_14);
lean_ctor_set(x_2, 0, x_49);
return x_2;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
lean_dec(x_2);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
x_52 = 1;
x_53 = 5;
x_54 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
x_55 = lean_usize_land(x_3, x_54);
x_56 = lean_usize_to_nat(x_55);
x_57 = lean_array_get_size(x_50);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_56);
lean_dec(x_51);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_50);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_array_fget(x_50, x_56);
x_61 = lean_box(0);
x_62 = lean_array_fset(x_50, x_56, x_61);
switch (lean_obj_tag(x_60)) {
case 0:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_1);
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_65 = x_60;
} else {
 lean_dec_ref(x_60);
 x_65 = lean_box(0);
}
lean_inc(x_63);
lean_inc(x_5);
x_66 = l_Lean_Meta_Grind_isCongruent(x_51, x_5, x_63);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_67 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_63, x_64, x_5, x_6);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_array_fset(x_62, x_56, x_68);
lean_dec(x_56);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_64);
lean_dec(x_63);
if (lean_is_scalar(x_65)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_65;
}
lean_ctor_set(x_71, 0, x_5);
lean_ctor_set(x_71, 1, x_6);
x_72 = lean_array_fset(x_62, x_56, x_71);
lean_dec(x_56);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
case 1:
{
lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_51);
x_74 = lean_ctor_get(x_60, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_75 = x_60;
} else {
 lean_dec_ref(x_60);
 x_75 = lean_box(0);
}
x_76 = lean_usize_shift_right(x_3, x_53);
x_77 = lean_usize_add(x_4, x_52);
x_78 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(x_1, x_74, x_76, x_77, x_5, x_6);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_75;
}
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_array_fset(x_62, x_56, x_79);
lean_dec(x_56);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
default: 
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_51);
lean_dec(x_1);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_5);
lean_ctor_set(x_82, 1, x_6);
x_83 = lean_array_fset(x_62, x_56, x_82);
lean_dec(x_56);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_2);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; size_t x_88; uint8_t x_89; 
x_86 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_87 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_addCongrTable___spec__7(x_1, x_2, x_86, x_5, x_6);
x_88 = 7;
x_89 = lean_usize_dec_le(x_88, x_4);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_87);
x_91 = lean_unsigned_to_nat(4u);
x_92 = lean_nat_dec_lt(x_90, x_91);
lean_dec(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_87, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec(x_87);
x_95 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1;
x_96 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_addCongrTable___spec__6(x_1, x_4, x_93, x_94, lean_box(0), x_86, x_95);
lean_dec(x_94);
lean_dec(x_93);
return x_96;
}
else
{
lean_dec(x_1);
return x_87;
}
}
else
{
lean_dec(x_1);
return x_87;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; size_t x_102; uint8_t x_103; 
x_97 = lean_ctor_get(x_2, 0);
x_98 = lean_ctor_get(x_2, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_2);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_101 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Grind_addCongrTable___spec__7(x_1, x_99, x_100, x_5, x_6);
x_102 = 7;
x_103 = lean_usize_dec_le(x_102, x_4);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_101);
x_105 = lean_unsigned_to_nat(4u);
x_106 = lean_nat_dec_lt(x_104, x_105);
lean_dec(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_101, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_101, 1);
lean_inc(x_108);
lean_dec(x_101);
x_109 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1;
x_110 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_addCongrTable___spec__6(x_1, x_4, x_107, x_108, lean_box(0), x_100, x_109);
lean_dec(x_108);
lean_dec(x_107);
return x_110;
}
else
{
lean_dec(x_1);
return x_101;
}
}
else
{
lean_dec(x_1);
return x_101;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_addCongrTable___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint64_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_inc(x_3);
x_6 = l_Lean_Meta_Grind_congrHash(x_5, x_3);
x_7 = lean_uint64_to_usize(x_6);
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(x_1, x_2, x_7, x_8, x_3, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_45; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_45 = l_Lean_Meta_Grind_hasSameType(x_1, x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = l_Lean_Meta_Grind_congrPlaceholderProof;
x_50 = 1;
lean_inc(x_2);
lean_inc(x_1);
x_51 = l_Lean_Meta_Grind_pushEqCore(x_1, x_2, x_49, x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_48);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_13 = x_52;
goto block_44;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_54 = l_Lean_Meta_Grind_congrPlaceholderProof;
x_55 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_56 = l_Lean_Meta_Grind_pushEqCore(x_1, x_2, x_54, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_53);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_13 = x_57;
goto block_44;
}
}
else
{
uint8_t x_58; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
block_44:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_st_ref_get(x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = l_Lean_Meta_Grind_Goal_getENode(x_15, x_1, x_10, x_11, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 3);
lean_dec(x_21);
lean_ctor_set(x_18, 3, x_2);
x_22 = l_Lean_Meta_Grind_setENode(x_1, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
x_25 = lean_ctor_get(x_18, 2);
x_26 = lean_ctor_get(x_18, 4);
x_27 = lean_ctor_get(x_18, 5);
x_28 = lean_ctor_get_uint8(x_18, sizeof(void*)*11);
x_29 = lean_ctor_get(x_18, 6);
x_30 = lean_ctor_get_uint8(x_18, sizeof(void*)*11 + 1);
x_31 = lean_ctor_get_uint8(x_18, sizeof(void*)*11 + 2);
x_32 = lean_ctor_get_uint8(x_18, sizeof(void*)*11 + 3);
x_33 = lean_ctor_get_uint8(x_18, sizeof(void*)*11 + 4);
x_34 = lean_ctor_get(x_18, 7);
x_35 = lean_ctor_get(x_18, 8);
x_36 = lean_ctor_get(x_18, 9);
x_37 = lean_ctor_get(x_18, 10);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_38 = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_24);
lean_ctor_set(x_38, 2, x_25);
lean_ctor_set(x_38, 3, x_2);
lean_ctor_set(x_38, 4, x_26);
lean_ctor_set(x_38, 5, x_27);
lean_ctor_set(x_38, 6, x_29);
lean_ctor_set(x_38, 7, x_34);
lean_ctor_set(x_38, 8, x_35);
lean_ctor_set(x_38, 9, x_36);
lean_ctor_set(x_38, 10, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*11, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*11 + 1, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*11 + 2, x_31);
lean_ctor_set_uint8(x_38, sizeof(void*)*11 + 3, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*11 + 4, x_33);
x_39 = l_Lean_Meta_Grind_setENode(x_1, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1;
x_2 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__2;
x_3 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" = ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__4;
x_14 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = l_Lean_Meta_Grind_addCongrTable___lambda__1(x_1, x_2, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 1);
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_1);
x_25 = l_Lean_MessageData_ofExpr(x_1);
x_26 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_25);
lean_ctor_set(x_14, 0, x_26);
x_27 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__8;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_2);
x_29 = l_Lean_MessageData_ofExpr(x_2);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_13, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_Grind_addCongrTable___lambda__1(x_1, x_2, x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_34);
lean_dec(x_33);
return x_35;
}
else
{
uint8_t x_36; 
lean_free_object(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_dec(x_14);
x_41 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_1);
x_43 = l_Lean_MessageData_ofExpr(x_1);
x_44 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__8;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_inc(x_2);
x_48 = l_Lean_MessageData_ofExpr(x_2);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
x_51 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_13, x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_42);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Meta_Grind_addCongrTable___lambda__1(x_1, x_2, x_52, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_53);
lean_dec(x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_41, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_57 = x_41;
} else {
 lean_dec_ref(x_41);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("found congruence between", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_addCongrTable___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nand", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_addCongrTable___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nbut functions have different types", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_addCongrTable___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_addCongrTable___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 4);
lean_inc(x_15);
lean_inc(x_1);
x_16 = l_Lean_PersistentHashMap_findEntry_x3f___at_Lean_Meta_Grind_addCongrTable___spec__1(x_13, x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_17 = lean_st_ref_take(x_2, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 4);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 5);
lean_inc(x_25);
x_26 = lean_ctor_get(x_18, 6);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_18, sizeof(void*)*26);
x_28 = lean_ctor_get(x_18, 7);
lean_inc(x_28);
x_29 = lean_ctor_get(x_18, 8);
lean_inc(x_29);
x_30 = lean_ctor_get(x_18, 9);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 10);
lean_inc(x_31);
x_32 = lean_ctor_get(x_18, 11);
lean_inc(x_32);
x_33 = lean_ctor_get(x_18, 12);
lean_inc(x_33);
x_34 = lean_ctor_get(x_18, 13);
lean_inc(x_34);
x_35 = lean_ctor_get(x_18, 14);
lean_inc(x_35);
x_36 = lean_ctor_get(x_18, 15);
lean_inc(x_36);
x_37 = lean_ctor_get(x_18, 16);
lean_inc(x_37);
x_38 = lean_ctor_get(x_18, 17);
lean_inc(x_38);
x_39 = lean_ctor_get(x_18, 18);
lean_inc(x_39);
x_40 = lean_ctor_get(x_18, 19);
lean_inc(x_40);
x_41 = lean_ctor_get(x_18, 20);
lean_inc(x_41);
x_42 = lean_ctor_get(x_18, 21);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 22);
lean_inc(x_43);
x_44 = lean_ctor_get(x_18, 23);
lean_inc(x_44);
x_45 = lean_ctor_get(x_18, 24);
lean_inc(x_45);
x_46 = lean_ctor_get(x_18, 25);
lean_inc(x_46);
x_47 = lean_box(0);
lean_inc(x_18);
x_48 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_addCongrTable___spec__4(x_18, x_24, x_1, x_47);
x_49 = !lean_is_exclusive(x_18);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_50 = lean_ctor_get(x_18, 25);
lean_dec(x_50);
x_51 = lean_ctor_get(x_18, 24);
lean_dec(x_51);
x_52 = lean_ctor_get(x_18, 23);
lean_dec(x_52);
x_53 = lean_ctor_get(x_18, 22);
lean_dec(x_53);
x_54 = lean_ctor_get(x_18, 21);
lean_dec(x_54);
x_55 = lean_ctor_get(x_18, 20);
lean_dec(x_55);
x_56 = lean_ctor_get(x_18, 19);
lean_dec(x_56);
x_57 = lean_ctor_get(x_18, 18);
lean_dec(x_57);
x_58 = lean_ctor_get(x_18, 17);
lean_dec(x_58);
x_59 = lean_ctor_get(x_18, 16);
lean_dec(x_59);
x_60 = lean_ctor_get(x_18, 15);
lean_dec(x_60);
x_61 = lean_ctor_get(x_18, 14);
lean_dec(x_61);
x_62 = lean_ctor_get(x_18, 13);
lean_dec(x_62);
x_63 = lean_ctor_get(x_18, 12);
lean_dec(x_63);
x_64 = lean_ctor_get(x_18, 11);
lean_dec(x_64);
x_65 = lean_ctor_get(x_18, 10);
lean_dec(x_65);
x_66 = lean_ctor_get(x_18, 9);
lean_dec(x_66);
x_67 = lean_ctor_get(x_18, 8);
lean_dec(x_67);
x_68 = lean_ctor_get(x_18, 7);
lean_dec(x_68);
x_69 = lean_ctor_get(x_18, 6);
lean_dec(x_69);
x_70 = lean_ctor_get(x_18, 5);
lean_dec(x_70);
x_71 = lean_ctor_get(x_18, 4);
lean_dec(x_71);
x_72 = lean_ctor_get(x_18, 3);
lean_dec(x_72);
x_73 = lean_ctor_get(x_18, 2);
lean_dec(x_73);
x_74 = lean_ctor_get(x_18, 1);
lean_dec(x_74);
x_75 = lean_ctor_get(x_18, 0);
lean_dec(x_75);
lean_ctor_set(x_18, 4, x_48);
x_76 = lean_st_ref_set(x_2, x_18, x_19);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set(x_76, 0, x_47);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_47);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_18);
x_81 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_81, 0, x_20);
lean_ctor_set(x_81, 1, x_21);
lean_ctor_set(x_81, 2, x_22);
lean_ctor_set(x_81, 3, x_23);
lean_ctor_set(x_81, 4, x_48);
lean_ctor_set(x_81, 5, x_25);
lean_ctor_set(x_81, 6, x_26);
lean_ctor_set(x_81, 7, x_28);
lean_ctor_set(x_81, 8, x_29);
lean_ctor_set(x_81, 9, x_30);
lean_ctor_set(x_81, 10, x_31);
lean_ctor_set(x_81, 11, x_32);
lean_ctor_set(x_81, 12, x_33);
lean_ctor_set(x_81, 13, x_34);
lean_ctor_set(x_81, 14, x_35);
lean_ctor_set(x_81, 15, x_36);
lean_ctor_set(x_81, 16, x_37);
lean_ctor_set(x_81, 17, x_38);
lean_ctor_set(x_81, 18, x_39);
lean_ctor_set(x_81, 19, x_40);
lean_ctor_set(x_81, 20, x_41);
lean_ctor_set(x_81, 21, x_42);
lean_ctor_set(x_81, 22, x_43);
lean_ctor_set(x_81, 23, x_44);
lean_ctor_set(x_81, 24, x_45);
lean_ctor_set(x_81, 25, x_46);
lean_ctor_set_uint8(x_81, sizeof(void*)*26, x_27);
x_82 = lean_st_ref_set(x_2, x_81, x_19);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_47);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_16, 0);
lean_inc(x_86);
lean_dec(x_16);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_ctor_get(x_86, 1);
lean_dec(x_89);
x_90 = l_Lean_Expr_getAppFn(x_1);
x_91 = l_Lean_Expr_getAppFn(x_88);
x_92 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_93 = l_Lean_Meta_Grind_hasSameType(x_90, x_91, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = l_Lean_indentExpr(x_1);
x_98 = l_Lean_Meta_Grind_addCongrTable___closed__2;
lean_ctor_set_tag(x_86, 7);
lean_ctor_set(x_86, 1, x_97);
lean_ctor_set(x_86, 0, x_98);
x_99 = l_Lean_Meta_Grind_addCongrTable___closed__4;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_99);
lean_ctor_set(x_11, 0, x_86);
x_100 = l_Lean_indentExpr(x_88);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_11);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_Meta_Grind_addCongrTable___closed__6;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_Meta_Grind_reportIssue(x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_96);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_104, 0);
lean_dec(x_106);
x_107 = lean_box(0);
lean_ctor_set(x_104, 0, x_107);
return x_104;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
lean_dec(x_104);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_free_object(x_86);
lean_free_object(x_11);
x_111 = lean_ctor_get(x_93, 1);
lean_inc(x_111);
lean_dec(x_93);
x_112 = lean_box(0);
x_113 = l_Lean_Meta_Grind_addCongrTable___lambda__2(x_1, x_88, x_112, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_111);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_free_object(x_86);
lean_dec(x_88);
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_93);
if (x_114 == 0)
{
return x_93;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_93, 0);
x_116 = lean_ctor_get(x_93, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_93);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_91);
lean_dec(x_90);
lean_free_object(x_86);
lean_free_object(x_11);
x_118 = lean_box(0);
x_119 = l_Lean_Meta_Grind_addCongrTable___lambda__2(x_1, x_88, x_118, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_120 = lean_ctor_get(x_86, 0);
lean_inc(x_120);
lean_dec(x_86);
x_121 = l_Lean_Expr_getAppFn(x_1);
x_122 = l_Lean_Expr_getAppFn(x_120);
x_123 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_124 = l_Lean_Meta_Grind_hasSameType(x_121, x_122, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = l_Lean_indentExpr(x_1);
x_129 = l_Lean_Meta_Grind_addCongrTable___closed__2;
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = l_Lean_Meta_Grind_addCongrTable___closed__4;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_131);
lean_ctor_set(x_11, 0, x_130);
x_132 = l_Lean_indentExpr(x_120);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_11);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Meta_Grind_addCongrTable___closed__6;
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_Meta_Grind_reportIssue(x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_127);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
x_139 = lean_box(0);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_free_object(x_11);
x_141 = lean_ctor_get(x_124, 1);
lean_inc(x_141);
lean_dec(x_124);
x_142 = lean_box(0);
x_143 = l_Lean_Meta_Grind_addCongrTable___lambda__2(x_1, x_120, x_142, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_141);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_120);
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_144 = lean_ctor_get(x_124, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_124, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_146 = x_124;
} else {
 lean_dec_ref(x_124);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_122);
lean_dec(x_121);
lean_free_object(x_11);
x_148 = lean_box(0);
x_149 = l_Lean_Meta_Grind_addCongrTable___lambda__2(x_1, x_120, x_148, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_149;
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_11, 0);
x_151 = lean_ctor_get(x_11, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_11);
x_152 = lean_ctor_get(x_150, 4);
lean_inc(x_152);
lean_inc(x_1);
x_153 = l_Lean_PersistentHashMap_findEntry_x3f___at_Lean_Meta_Grind_addCongrTable___spec__1(x_150, x_152, x_1);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_154 = lean_st_ref_take(x_2, x_151);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_155, 3);
lean_inc(x_160);
x_161 = lean_ctor_get(x_155, 4);
lean_inc(x_161);
x_162 = lean_ctor_get(x_155, 5);
lean_inc(x_162);
x_163 = lean_ctor_get(x_155, 6);
lean_inc(x_163);
x_164 = lean_ctor_get_uint8(x_155, sizeof(void*)*26);
x_165 = lean_ctor_get(x_155, 7);
lean_inc(x_165);
x_166 = lean_ctor_get(x_155, 8);
lean_inc(x_166);
x_167 = lean_ctor_get(x_155, 9);
lean_inc(x_167);
x_168 = lean_ctor_get(x_155, 10);
lean_inc(x_168);
x_169 = lean_ctor_get(x_155, 11);
lean_inc(x_169);
x_170 = lean_ctor_get(x_155, 12);
lean_inc(x_170);
x_171 = lean_ctor_get(x_155, 13);
lean_inc(x_171);
x_172 = lean_ctor_get(x_155, 14);
lean_inc(x_172);
x_173 = lean_ctor_get(x_155, 15);
lean_inc(x_173);
x_174 = lean_ctor_get(x_155, 16);
lean_inc(x_174);
x_175 = lean_ctor_get(x_155, 17);
lean_inc(x_175);
x_176 = lean_ctor_get(x_155, 18);
lean_inc(x_176);
x_177 = lean_ctor_get(x_155, 19);
lean_inc(x_177);
x_178 = lean_ctor_get(x_155, 20);
lean_inc(x_178);
x_179 = lean_ctor_get(x_155, 21);
lean_inc(x_179);
x_180 = lean_ctor_get(x_155, 22);
lean_inc(x_180);
x_181 = lean_ctor_get(x_155, 23);
lean_inc(x_181);
x_182 = lean_ctor_get(x_155, 24);
lean_inc(x_182);
x_183 = lean_ctor_get(x_155, 25);
lean_inc(x_183);
x_184 = lean_box(0);
lean_inc(x_155);
x_185 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_addCongrTable___spec__4(x_155, x_161, x_1, x_184);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 lean_ctor_release(x_155, 3);
 lean_ctor_release(x_155, 4);
 lean_ctor_release(x_155, 5);
 lean_ctor_release(x_155, 6);
 lean_ctor_release(x_155, 7);
 lean_ctor_release(x_155, 8);
 lean_ctor_release(x_155, 9);
 lean_ctor_release(x_155, 10);
 lean_ctor_release(x_155, 11);
 lean_ctor_release(x_155, 12);
 lean_ctor_release(x_155, 13);
 lean_ctor_release(x_155, 14);
 lean_ctor_release(x_155, 15);
 lean_ctor_release(x_155, 16);
 lean_ctor_release(x_155, 17);
 lean_ctor_release(x_155, 18);
 lean_ctor_release(x_155, 19);
 lean_ctor_release(x_155, 20);
 lean_ctor_release(x_155, 21);
 lean_ctor_release(x_155, 22);
 lean_ctor_release(x_155, 23);
 lean_ctor_release(x_155, 24);
 lean_ctor_release(x_155, 25);
 x_186 = x_155;
} else {
 lean_dec_ref(x_155);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(0, 26, 1);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_157);
lean_ctor_set(x_187, 1, x_158);
lean_ctor_set(x_187, 2, x_159);
lean_ctor_set(x_187, 3, x_160);
lean_ctor_set(x_187, 4, x_185);
lean_ctor_set(x_187, 5, x_162);
lean_ctor_set(x_187, 6, x_163);
lean_ctor_set(x_187, 7, x_165);
lean_ctor_set(x_187, 8, x_166);
lean_ctor_set(x_187, 9, x_167);
lean_ctor_set(x_187, 10, x_168);
lean_ctor_set(x_187, 11, x_169);
lean_ctor_set(x_187, 12, x_170);
lean_ctor_set(x_187, 13, x_171);
lean_ctor_set(x_187, 14, x_172);
lean_ctor_set(x_187, 15, x_173);
lean_ctor_set(x_187, 16, x_174);
lean_ctor_set(x_187, 17, x_175);
lean_ctor_set(x_187, 18, x_176);
lean_ctor_set(x_187, 19, x_177);
lean_ctor_set(x_187, 20, x_178);
lean_ctor_set(x_187, 21, x_179);
lean_ctor_set(x_187, 22, x_180);
lean_ctor_set(x_187, 23, x_181);
lean_ctor_set(x_187, 24, x_182);
lean_ctor_set(x_187, 25, x_183);
lean_ctor_set_uint8(x_187, sizeof(void*)*26, x_164);
x_188 = lean_st_ref_set(x_2, x_187, x_156);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_184);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_192 = lean_ctor_get(x_153, 0);
lean_inc(x_192);
lean_dec(x_153);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
x_195 = l_Lean_Expr_getAppFn(x_1);
x_196 = l_Lean_Expr_getAppFn(x_193);
x_197 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_195, x_196);
if (x_197 == 0)
{
lean_object* x_198; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_198 = l_Lean_Meta_Grind_hasSameType(x_195, x_196, x_6, x_7, x_8, x_9, x_151);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; uint8_t x_200; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_unbox(x_199);
lean_dec(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec(x_198);
x_202 = l_Lean_indentExpr(x_1);
x_203 = l_Lean_Meta_Grind_addCongrTable___closed__2;
if (lean_is_scalar(x_194)) {
 x_204 = lean_alloc_ctor(7, 2, 0);
} else {
 x_204 = x_194;
 lean_ctor_set_tag(x_204, 7);
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
x_205 = l_Lean_Meta_Grind_addCongrTable___closed__4;
x_206 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = l_Lean_indentExpr(x_193);
x_208 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Lean_Meta_Grind_addCongrTable___closed__6;
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_Meta_Grind_reportIssue(x_210, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_201);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_213 = x_211;
} else {
 lean_dec_ref(x_211);
 x_213 = lean_box(0);
}
x_214 = lean_box(0);
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_212);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_194);
x_216 = lean_ctor_get(x_198, 1);
lean_inc(x_216);
lean_dec(x_198);
x_217 = lean_box(0);
x_218 = l_Lean_Meta_Grind_addCongrTable___lambda__2(x_1, x_193, x_217, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_216);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_219 = lean_ctor_get(x_198, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_198, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_221 = x_198;
} else {
 lean_dec_ref(x_198);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
x_223 = lean_box(0);
x_224 = l_Lean_Meta_Grind_addCongrTable___lambda__2(x_1, x_193, x_223, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_151);
return x_224;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___at_Lean_Meta_Grind_addCongrTable___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findEntryAtAux___at_Lean_Meta_Grind_addCongrTable___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_addCongrTable___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Grind_addCongrTable___spec__6(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_addCongrTable___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_addCongrTable___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addCongrTable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_addCongrTable(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__3(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_HeadIndex_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_HeadIndex_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__7(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__6(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__7(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__6(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_HeadIndex_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_11 = l_Lean_Expr_toHeadIndex(x_1);
x_12 = lean_st_ref_take(x_2, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_14, 5);
lean_inc(x_17);
x_18 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1(x_17, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_box(0);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_1);
x_20 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(x_17, x_11, x_12);
lean_ctor_set(x_14, 5, x_20);
x_21 = lean_st_ref_set(x_2, x_14, x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_28);
lean_ctor_set(x_12, 0, x_1);
x_29 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(x_17, x_11, x_12);
lean_ctor_set(x_14, 5, x_29);
x_30 = lean_st_ref_set(x_2, x_14, x_16);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_37 = lean_ctor_get(x_12, 1);
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
x_40 = lean_ctor_get(x_14, 2);
x_41 = lean_ctor_get(x_14, 3);
x_42 = lean_ctor_get(x_14, 4);
x_43 = lean_ctor_get(x_14, 5);
x_44 = lean_ctor_get(x_14, 6);
x_45 = lean_ctor_get_uint8(x_14, sizeof(void*)*26);
x_46 = lean_ctor_get(x_14, 7);
x_47 = lean_ctor_get(x_14, 8);
x_48 = lean_ctor_get(x_14, 9);
x_49 = lean_ctor_get(x_14, 10);
x_50 = lean_ctor_get(x_14, 11);
x_51 = lean_ctor_get(x_14, 12);
x_52 = lean_ctor_get(x_14, 13);
x_53 = lean_ctor_get(x_14, 14);
x_54 = lean_ctor_get(x_14, 15);
x_55 = lean_ctor_get(x_14, 16);
x_56 = lean_ctor_get(x_14, 17);
x_57 = lean_ctor_get(x_14, 18);
x_58 = lean_ctor_get(x_14, 19);
x_59 = lean_ctor_get(x_14, 20);
x_60 = lean_ctor_get(x_14, 21);
x_61 = lean_ctor_get(x_14, 22);
x_62 = lean_ctor_get(x_14, 23);
x_63 = lean_ctor_get(x_14, 24);
x_64 = lean_ctor_get(x_14, 25);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
lean_inc(x_43);
x_65 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1(x_43, x_11);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_box(0);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_66);
lean_ctor_set(x_12, 0, x_1);
x_67 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(x_43, x_11, x_12);
x_68 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_68, 0, x_38);
lean_ctor_set(x_68, 1, x_39);
lean_ctor_set(x_68, 2, x_40);
lean_ctor_set(x_68, 3, x_41);
lean_ctor_set(x_68, 4, x_42);
lean_ctor_set(x_68, 5, x_67);
lean_ctor_set(x_68, 6, x_44);
lean_ctor_set(x_68, 7, x_46);
lean_ctor_set(x_68, 8, x_47);
lean_ctor_set(x_68, 9, x_48);
lean_ctor_set(x_68, 10, x_49);
lean_ctor_set(x_68, 11, x_50);
lean_ctor_set(x_68, 12, x_51);
lean_ctor_set(x_68, 13, x_52);
lean_ctor_set(x_68, 14, x_53);
lean_ctor_set(x_68, 15, x_54);
lean_ctor_set(x_68, 16, x_55);
lean_ctor_set(x_68, 17, x_56);
lean_ctor_set(x_68, 18, x_57);
lean_ctor_set(x_68, 19, x_58);
lean_ctor_set(x_68, 20, x_59);
lean_ctor_set(x_68, 21, x_60);
lean_ctor_set(x_68, 22, x_61);
lean_ctor_set(x_68, 23, x_62);
lean_ctor_set(x_68, 24, x_63);
lean_ctor_set(x_68, 25, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*26, x_45);
x_69 = lean_st_ref_set(x_2, x_68, x_37);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_65, 0);
lean_inc(x_74);
lean_dec(x_65);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_74);
lean_ctor_set(x_12, 0, x_1);
x_75 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(x_43, x_11, x_12);
x_76 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_76, 0, x_38);
lean_ctor_set(x_76, 1, x_39);
lean_ctor_set(x_76, 2, x_40);
lean_ctor_set(x_76, 3, x_41);
lean_ctor_set(x_76, 4, x_42);
lean_ctor_set(x_76, 5, x_75);
lean_ctor_set(x_76, 6, x_44);
lean_ctor_set(x_76, 7, x_46);
lean_ctor_set(x_76, 8, x_47);
lean_ctor_set(x_76, 9, x_48);
lean_ctor_set(x_76, 10, x_49);
lean_ctor_set(x_76, 11, x_50);
lean_ctor_set(x_76, 12, x_51);
lean_ctor_set(x_76, 13, x_52);
lean_ctor_set(x_76, 14, x_53);
lean_ctor_set(x_76, 15, x_54);
lean_ctor_set(x_76, 16, x_55);
lean_ctor_set(x_76, 17, x_56);
lean_ctor_set(x_76, 18, x_57);
lean_ctor_set(x_76, 19, x_58);
lean_ctor_set(x_76, 20, x_59);
lean_ctor_set(x_76, 21, x_60);
lean_ctor_set(x_76, 22, x_61);
lean_ctor_set(x_76, 23, x_62);
lean_ctor_set(x_76, 24, x_63);
lean_ctor_set(x_76, 25, x_64);
lean_ctor_set_uint8(x_76, sizeof(void*)*26, x_45);
x_77 = lean_st_ref_set(x_2, x_76, x_37);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_box(0);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_82 = lean_ctor_get(x_12, 0);
x_83 = lean_ctor_get(x_12, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_12);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_82, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_82, 4);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 5);
lean_inc(x_89);
x_90 = lean_ctor_get(x_82, 6);
lean_inc(x_90);
x_91 = lean_ctor_get_uint8(x_82, sizeof(void*)*26);
x_92 = lean_ctor_get(x_82, 7);
lean_inc(x_92);
x_93 = lean_ctor_get(x_82, 8);
lean_inc(x_93);
x_94 = lean_ctor_get(x_82, 9);
lean_inc(x_94);
x_95 = lean_ctor_get(x_82, 10);
lean_inc(x_95);
x_96 = lean_ctor_get(x_82, 11);
lean_inc(x_96);
x_97 = lean_ctor_get(x_82, 12);
lean_inc(x_97);
x_98 = lean_ctor_get(x_82, 13);
lean_inc(x_98);
x_99 = lean_ctor_get(x_82, 14);
lean_inc(x_99);
x_100 = lean_ctor_get(x_82, 15);
lean_inc(x_100);
x_101 = lean_ctor_get(x_82, 16);
lean_inc(x_101);
x_102 = lean_ctor_get(x_82, 17);
lean_inc(x_102);
x_103 = lean_ctor_get(x_82, 18);
lean_inc(x_103);
x_104 = lean_ctor_get(x_82, 19);
lean_inc(x_104);
x_105 = lean_ctor_get(x_82, 20);
lean_inc(x_105);
x_106 = lean_ctor_get(x_82, 21);
lean_inc(x_106);
x_107 = lean_ctor_get(x_82, 22);
lean_inc(x_107);
x_108 = lean_ctor_get(x_82, 23);
lean_inc(x_108);
x_109 = lean_ctor_get(x_82, 24);
lean_inc(x_109);
x_110 = lean_ctor_get(x_82, 25);
lean_inc(x_110);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 lean_ctor_release(x_82, 3);
 lean_ctor_release(x_82, 4);
 lean_ctor_release(x_82, 5);
 lean_ctor_release(x_82, 6);
 lean_ctor_release(x_82, 7);
 lean_ctor_release(x_82, 8);
 lean_ctor_release(x_82, 9);
 lean_ctor_release(x_82, 10);
 lean_ctor_release(x_82, 11);
 lean_ctor_release(x_82, 12);
 lean_ctor_release(x_82, 13);
 lean_ctor_release(x_82, 14);
 lean_ctor_release(x_82, 15);
 lean_ctor_release(x_82, 16);
 lean_ctor_release(x_82, 17);
 lean_ctor_release(x_82, 18);
 lean_ctor_release(x_82, 19);
 lean_ctor_release(x_82, 20);
 lean_ctor_release(x_82, 21);
 lean_ctor_release(x_82, 22);
 lean_ctor_release(x_82, 23);
 lean_ctor_release(x_82, 24);
 lean_ctor_release(x_82, 25);
 x_111 = x_82;
} else {
 lean_dec_ref(x_82);
 x_111 = lean_box(0);
}
lean_inc(x_89);
x_112 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1(x_89, x_11);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_1);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(x_89, x_11, x_114);
if (lean_is_scalar(x_111)) {
 x_116 = lean_alloc_ctor(0, 26, 1);
} else {
 x_116 = x_111;
}
lean_ctor_set(x_116, 0, x_84);
lean_ctor_set(x_116, 1, x_85);
lean_ctor_set(x_116, 2, x_86);
lean_ctor_set(x_116, 3, x_87);
lean_ctor_set(x_116, 4, x_88);
lean_ctor_set(x_116, 5, x_115);
lean_ctor_set(x_116, 6, x_90);
lean_ctor_set(x_116, 7, x_92);
lean_ctor_set(x_116, 8, x_93);
lean_ctor_set(x_116, 9, x_94);
lean_ctor_set(x_116, 10, x_95);
lean_ctor_set(x_116, 11, x_96);
lean_ctor_set(x_116, 12, x_97);
lean_ctor_set(x_116, 13, x_98);
lean_ctor_set(x_116, 14, x_99);
lean_ctor_set(x_116, 15, x_100);
lean_ctor_set(x_116, 16, x_101);
lean_ctor_set(x_116, 17, x_102);
lean_ctor_set(x_116, 18, x_103);
lean_ctor_set(x_116, 19, x_104);
lean_ctor_set(x_116, 20, x_105);
lean_ctor_set(x_116, 21, x_106);
lean_ctor_set(x_116, 22, x_107);
lean_ctor_set(x_116, 23, x_108);
lean_ctor_set(x_116, 24, x_109);
lean_ctor_set(x_116, 25, x_110);
lean_ctor_set_uint8(x_116, sizeof(void*)*26, x_91);
x_117 = lean_st_ref_set(x_2, x_116, x_83);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_122 = lean_ctor_get(x_112, 0);
lean_inc(x_122);
lean_dec(x_112);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_1);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__4(x_89, x_11, x_123);
if (lean_is_scalar(x_111)) {
 x_125 = lean_alloc_ctor(0, 26, 1);
} else {
 x_125 = x_111;
}
lean_ctor_set(x_125, 0, x_84);
lean_ctor_set(x_125, 1, x_85);
lean_ctor_set(x_125, 2, x_86);
lean_ctor_set(x_125, 3, x_87);
lean_ctor_set(x_125, 4, x_88);
lean_ctor_set(x_125, 5, x_124);
lean_ctor_set(x_125, 6, x_90);
lean_ctor_set(x_125, 7, x_92);
lean_ctor_set(x_125, 8, x_93);
lean_ctor_set(x_125, 9, x_94);
lean_ctor_set(x_125, 10, x_95);
lean_ctor_set(x_125, 11, x_96);
lean_ctor_set(x_125, 12, x_97);
lean_ctor_set(x_125, 13, x_98);
lean_ctor_set(x_125, 14, x_99);
lean_ctor_set(x_125, 15, x_100);
lean_ctor_set(x_125, 16, x_101);
lean_ctor_set(x_125, 17, x_102);
lean_ctor_set(x_125, 18, x_103);
lean_ctor_set(x_125, 19, x_104);
lean_ctor_set(x_125, 20, x_105);
lean_ctor_set(x_125, 21, x_106);
lean_ctor_set(x_125, 22, x_107);
lean_ctor_set(x_125, 23, x_108);
lean_ctor_set(x_125, 24, x_109);
lean_ctor_set(x_125, 25, x_110);
lean_ctor_set_uint8(x_125, sizeof(void*)*26, x_91);
x_126 = lean_st_ref_set(x_2, x_125, x_83);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
x_129 = lean_box(0);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_127);
return x_130;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__6(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_take(x_3, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_14, 19);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_17);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_14, 19, x_12);
x_18 = lean_st_ref_set(x_3, x_14, x_16);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_25 = lean_ctor_get(x_12, 1);
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
x_28 = lean_ctor_get(x_14, 2);
x_29 = lean_ctor_get(x_14, 3);
x_30 = lean_ctor_get(x_14, 4);
x_31 = lean_ctor_get(x_14, 5);
x_32 = lean_ctor_get(x_14, 6);
x_33 = lean_ctor_get_uint8(x_14, sizeof(void*)*26);
x_34 = lean_ctor_get(x_14, 7);
x_35 = lean_ctor_get(x_14, 8);
x_36 = lean_ctor_get(x_14, 9);
x_37 = lean_ctor_get(x_14, 10);
x_38 = lean_ctor_get(x_14, 11);
x_39 = lean_ctor_get(x_14, 12);
x_40 = lean_ctor_get(x_14, 13);
x_41 = lean_ctor_get(x_14, 14);
x_42 = lean_ctor_get(x_14, 15);
x_43 = lean_ctor_get(x_14, 16);
x_44 = lean_ctor_get(x_14, 17);
x_45 = lean_ctor_get(x_14, 18);
x_46 = lean_ctor_get(x_14, 19);
x_47 = lean_ctor_get(x_14, 20);
x_48 = lean_ctor_get(x_14, 21);
x_49 = lean_ctor_get(x_14, 22);
x_50 = lean_ctor_get(x_14, 23);
x_51 = lean_ctor_get(x_14, 24);
x_52 = lean_ctor_get(x_14, 25);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_46);
lean_ctor_set(x_12, 0, x_1);
x_53 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_53, 0, x_26);
lean_ctor_set(x_53, 1, x_27);
lean_ctor_set(x_53, 2, x_28);
lean_ctor_set(x_53, 3, x_29);
lean_ctor_set(x_53, 4, x_30);
lean_ctor_set(x_53, 5, x_31);
lean_ctor_set(x_53, 6, x_32);
lean_ctor_set(x_53, 7, x_34);
lean_ctor_set(x_53, 8, x_35);
lean_ctor_set(x_53, 9, x_36);
lean_ctor_set(x_53, 10, x_37);
lean_ctor_set(x_53, 11, x_38);
lean_ctor_set(x_53, 12, x_39);
lean_ctor_set(x_53, 13, x_40);
lean_ctor_set(x_53, 14, x_41);
lean_ctor_set(x_53, 15, x_42);
lean_ctor_set(x_53, 16, x_43);
lean_ctor_set(x_53, 17, x_44);
lean_ctor_set(x_53, 18, x_45);
lean_ctor_set(x_53, 19, x_12);
lean_ctor_set(x_53, 20, x_47);
lean_ctor_set(x_53, 21, x_48);
lean_ctor_set(x_53, 22, x_49);
lean_ctor_set(x_53, 23, x_50);
lean_ctor_set(x_53, 24, x_51);
lean_ctor_set(x_53, 25, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*26, x_33);
x_54 = lean_st_ref_set(x_3, x_53, x_25);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_59 = lean_ctor_get(x_12, 0);
x_60 = lean_ctor_get(x_12, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_12);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 5);
lean_inc(x_66);
x_67 = lean_ctor_get(x_59, 6);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_59, sizeof(void*)*26);
x_69 = lean_ctor_get(x_59, 7);
lean_inc(x_69);
x_70 = lean_ctor_get(x_59, 8);
lean_inc(x_70);
x_71 = lean_ctor_get(x_59, 9);
lean_inc(x_71);
x_72 = lean_ctor_get(x_59, 10);
lean_inc(x_72);
x_73 = lean_ctor_get(x_59, 11);
lean_inc(x_73);
x_74 = lean_ctor_get(x_59, 12);
lean_inc(x_74);
x_75 = lean_ctor_get(x_59, 13);
lean_inc(x_75);
x_76 = lean_ctor_get(x_59, 14);
lean_inc(x_76);
x_77 = lean_ctor_get(x_59, 15);
lean_inc(x_77);
x_78 = lean_ctor_get(x_59, 16);
lean_inc(x_78);
x_79 = lean_ctor_get(x_59, 17);
lean_inc(x_79);
x_80 = lean_ctor_get(x_59, 18);
lean_inc(x_80);
x_81 = lean_ctor_get(x_59, 19);
lean_inc(x_81);
x_82 = lean_ctor_get(x_59, 20);
lean_inc(x_82);
x_83 = lean_ctor_get(x_59, 21);
lean_inc(x_83);
x_84 = lean_ctor_get(x_59, 22);
lean_inc(x_84);
x_85 = lean_ctor_get(x_59, 23);
lean_inc(x_85);
x_86 = lean_ctor_get(x_59, 24);
lean_inc(x_86);
x_87 = lean_ctor_get(x_59, 25);
lean_inc(x_87);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 lean_ctor_release(x_59, 5);
 lean_ctor_release(x_59, 6);
 lean_ctor_release(x_59, 7);
 lean_ctor_release(x_59, 8);
 lean_ctor_release(x_59, 9);
 lean_ctor_release(x_59, 10);
 lean_ctor_release(x_59, 11);
 lean_ctor_release(x_59, 12);
 lean_ctor_release(x_59, 13);
 lean_ctor_release(x_59, 14);
 lean_ctor_release(x_59, 15);
 lean_ctor_release(x_59, 16);
 lean_ctor_release(x_59, 17);
 lean_ctor_release(x_59, 18);
 lean_ctor_release(x_59, 19);
 lean_ctor_release(x_59, 20);
 lean_ctor_release(x_59, 21);
 lean_ctor_release(x_59, 22);
 lean_ctor_release(x_59, 23);
 lean_ctor_release(x_59, 24);
 lean_ctor_release(x_59, 25);
 x_88 = x_59;
} else {
 lean_dec_ref(x_59);
 x_88 = lean_box(0);
}
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_81);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 26, 1);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_61);
lean_ctor_set(x_90, 1, x_62);
lean_ctor_set(x_90, 2, x_63);
lean_ctor_set(x_90, 3, x_64);
lean_ctor_set(x_90, 4, x_65);
lean_ctor_set(x_90, 5, x_66);
lean_ctor_set(x_90, 6, x_67);
lean_ctor_set(x_90, 7, x_69);
lean_ctor_set(x_90, 8, x_70);
lean_ctor_set(x_90, 9, x_71);
lean_ctor_set(x_90, 10, x_72);
lean_ctor_set(x_90, 11, x_73);
lean_ctor_set(x_90, 12, x_74);
lean_ctor_set(x_90, 13, x_75);
lean_ctor_set(x_90, 14, x_76);
lean_ctor_set(x_90, 15, x_77);
lean_ctor_set(x_90, 16, x_78);
lean_ctor_set(x_90, 17, x_79);
lean_ctor_set(x_90, 18, x_80);
lean_ctor_set(x_90, 19, x_89);
lean_ctor_set(x_90, 20, x_82);
lean_ctor_set(x_90, 21, x_83);
lean_ctor_set(x_90, 22, x_84);
lean_ctor_set(x_90, 23, x_85);
lean_ctor_set(x_90, 24, x_86);
lean_ctor_set(x_90, 25, x_87);
lean_ctor_set_uint8(x_90, sizeof(void*)*26, x_68);
x_91 = lean_st_ref_set(x_3, x_90, x_60);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("candidate", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__3;
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1(x_1, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_1);
x_23 = l_Lean_MessageData_ofExpr(x_1);
x_24 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_23);
lean_ctor_set(x_12, 0, x_24);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_11, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1(x_1, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
lean_dec(x_27);
return x_29;
}
else
{
uint8_t x_30; 
lean_free_object(x_12);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_dec(x_12);
x_35 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_1);
x_37 = l_Lean_MessageData_ofExpr(x_1);
x_38 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_11, x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1(x_1, x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_47 = x_35;
} else {
 lean_dec_ref(x_35);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__4;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__12;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMorallyIff(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_appFnCleanup(x_2, lean_box(0));
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Expr_appFnCleanup(x_5, lean_box(0));
x_9 = l_Lean_Expr_isApp(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_Expr_appArg(x_8, lean_box(0));
x_12 = l_Lean_Expr_appFnCleanup(x_8, lean_box(0));
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__2;
x_14 = l_Lean_Expr_isConstOf(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
x_15 = 0;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = l_Lean_Expr_isProp(x_11);
lean_dec(x_11);
return x_16;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMorallyIff___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isMorallyIff(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Meta_isMatcherAppCore(x_14, x_1);
x_16 = lean_box(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_isMatcherAppCore(x_19, x_1);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 10);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Grind_CasesTypes_isSplit(x_16, x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Meta_Grind_getConfig___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*6 + 3);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
return x_28;
}
}
else
{
lean_object* x_29; 
x_29 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Lean_Meta_isInductivePredicate(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__1(x_1, x_2, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes;
x_15 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__2(x_13, x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Meta_Grind_getConfig___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*6 + 1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__3(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = l_Lean_Meta_isMatcherApp___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__3(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_26 = l_Lean_Meta_reduceMatcher_x3f(x_1, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_27);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_dec(x_26);
x_35 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 0);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_26);
if (x_46 == 0)
{
return x_26;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_26, 0);
x_48 = lean_ctor_get(x_26, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_26);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
lean_inc(x_1);
x_12 = l_Lean_Meta_Grind_isMorallyIff(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__4(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_11 = lean_infer_type(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Expr_getAppFn(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_free_object(x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_2, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_19, 10);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_Grind_CasesTypes_isSplit(x_21, x_16);
lean_dec(x_16);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = lean_box(0);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; 
lean_free_object(x_17);
x_24 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_ctor_get(x_25, 10);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_Grind_CasesTypes_isSplit(x_27, x_16);
lean_dec(x_16);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_32 = lean_box(0);
lean_ctor_set(x_11, 0, x_32);
return x_11;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = l_Lean_Expr_getAppFn(x_33);
lean_dec(x_33);
if (lean_obj_tag(x_35) == 4)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_2, x_34);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_38, 10);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Meta_Grind_CasesTypes_isSplit(x_41, x_36);
lean_dec(x_36);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_40;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec(x_40);
x_45 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_34);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
return x_11;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
case 5:
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = l_Lean_Meta_Grind_getConfig___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*6 + 2);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_box(0);
x_57 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__5(x_1, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_55);
return x_57;
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = l_Lean_Expr_isIte(x_1);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = l_Lean_Expr_isDIte(x_1);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_box(0);
x_62 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__5(x_1, x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_58);
return x_62;
}
else
{
lean_object* x_63; 
x_63 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set(x_63, 0, x_66);
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_63);
if (x_70 == 0)
{
return x_63;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_63, 0);
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_63);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; 
x_74 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_74);
if (x_81 == 0)
{
return x_74;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_74, 0);
x_83 = lean_ctor_get(x_74, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_74);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
default: 
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_10);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_isMatcherApp___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqRecOn_heq", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = l_Lean_Expr_constLevels_x21(x_2);
x_19 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__4;
x_20 = l_Lean_Expr_const___override(x_19, x_18);
lean_inc(x_8);
x_21 = l_Lean_mkApp6(x_20, x_3, x_4, x_5, x_6, x_7, x_8);
x_22 = 1;
x_23 = l_Lean_Meta_Grind_pushEqCore(x_1, x_8, x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_23;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqNDRec_heq", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = l_Lean_Expr_constLevels_x21(x_2);
x_19 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__2;
x_20 = l_Lean_Expr_const___override(x_19, x_18);
lean_inc(x_6);
x_21 = l_Lean_mkApp6(x_20, x_3, x_4, x_5, x_6, x_7, x_8);
x_22 = 1;
x_23 = l_Lean_Meta_Grind_pushEqCore(x_1, x_6, x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_23;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqRec_heq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = l_Lean_Expr_constLevels_x21(x_2);
x_19 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__2;
x_20 = l_Lean_Expr_const___override(x_19, x_18);
lean_inc(x_6);
x_21 = l_Lean_mkApp6(x_20, x_3, x_4, x_5, x_6, x_7, x_8);
x_22 = 1;
x_23 = l_Lean_Meta_Grind_pushEqCore(x_1, x_6, x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_23;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cast_heq", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = l_Lean_Expr_constLevels_x21(x_2);
x_17 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__2;
x_18 = l_Lean_Expr_const___override(x_17, x_16);
lean_inc(x_6);
x_19 = l_Lean_mkApp4(x_18, x_3, x_4, x_5, x_6);
x_20 = 1;
x_21 = l_Lean_Meta_Grind_pushEqCore(x_1, x_6, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__5___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cast", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recOn", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ndrec", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rec", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp(x_1, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__1;
x_15 = l_Lean_Expr_cleanupAnnotations(x_12);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_apply_10(x_14, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Expr_appArg(x_15, lean_box(0));
x_20 = l_Lean_Expr_appFnCleanup(x_15, lean_box(0));
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_apply_10(x_14, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Expr_appArg(x_20, lean_box(0));
x_25 = l_Lean_Expr_appFnCleanup(x_20, lean_box(0));
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_apply_10(x_14, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Expr_appArg(x_25, lean_box(0));
x_30 = l_Lean_Expr_appFnCleanup(x_25, lean_box(0));
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = lean_apply_10(x_14, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_Lean_Expr_appArg(x_30, lean_box(0));
x_35 = l_Lean_Expr_appFnCleanup(x_30, lean_box(0));
x_36 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__3;
x_37 = l_Lean_Expr_isConstOf(x_35, x_36);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_Lean_Expr_isApp(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_1);
x_39 = lean_box(0);
x_40 = lean_apply_10(x_14, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Lean_Expr_appArg(x_35, lean_box(0));
x_42 = l_Lean_Expr_appFnCleanup(x_35, lean_box(0));
x_43 = l_Lean_Expr_isApp(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_1);
x_44 = lean_box(0);
x_45 = lean_apply_10(x_14, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = l_Lean_Expr_appArg(x_42, lean_box(0));
x_47 = l_Lean_Expr_appFnCleanup(x_42, lean_box(0));
x_48 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__5;
x_49 = l_Lean_Expr_isConstOf(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__7;
x_51 = l_Lean_Expr_isConstOf(x_47, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__9;
x_53 = l_Lean_Expr_isConstOf(x_47, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = lean_apply_10(x_14, x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_55;
}
else
{
lean_object* x_56; 
x_56 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3(x_1, x_47, x_46, x_41, x_34, x_29, x_24, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_47);
return x_56;
}
}
else
{
lean_object* x_57; 
x_57 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2(x_1, x_47, x_46, x_41, x_34, x_29, x_24, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_47);
return x_57;
}
}
else
{
lean_object* x_58; 
x_58 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1(x_1, x_47, x_46, x_41, x_34, x_29, x_24, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_47);
return x_58;
}
}
}
}
else
{
lean_object* x_59; 
x_59 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4(x_1, x_35, x_34, x_29, x_24, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_35);
return x_59;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible___lambda__2), 6, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible___lambda__3___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_normalizeLevels___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__2___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__1;
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Core_transform___at_Lean_Meta_Grind_unfoldReducible___spec__1(x_1, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__3;
x_17 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__4;
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_14, x_16, x_17, x_8, x_9, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Lean_Meta_Grind_canon(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_Grind_shareCommon(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_mkENode_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
x_13 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_12, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_mkENode_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_mkENode_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_uget(x_4, x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_4, x_3, x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_19 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern(x_16, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_array_uset(x_18, x_3, x_20);
x_3 = x_23;
x_4 = x_24;
x_13 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_array_set(x_3, x_4, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_4, x_17);
lean_dec(x_4);
x_2 = x_14;
x_3 = x_16;
x_4 = x_18;
goto _start;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
lean_dec(x_4);
x_20 = lean_array_size(x_3);
x_21 = 0;
x_22 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__1(x_1, x_20, x_21, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_mkAppN(x_2, x_24);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = l_Lean_mkAppN(x_2, x_26);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isBVar(x_1);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare;
x_14 = lean_expr_eqv(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_groundPattern_x3f(x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_16);
x_18 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1;
lean_inc(x_17);
x_19 = lean_mk_array(x_17, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_17, x_20);
lean_dec(x_17);
x_22 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__2(x_2, x_1, x_19, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_24 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
lean_inc(x_25);
x_28 = l_Lean_Meta_Grind_internalize(x_25, x_2, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = l_Lean_Meta_Grind_mkGroundPattern(x_25);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = l_Lean_Meta_Grind_mkGroundPattern(x_25);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_25);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_28, 0);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_28);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_11);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_internalize___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_nat_dec_lt(x_7, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_6);
x_22 = lean_array_fget(x_3, x_7);
lean_inc(x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_1);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_22);
x_24 = l_Lean_Meta_Grind_internalize(x_22, x_2, x_23, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_1);
x_26 = l_Lean_Meta_Grind_registerParent(x_1, x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_5, 2);
x_29 = lean_nat_add(x_7, x_28);
lean_dec(x_7);
x_30 = lean_box(0);
x_6 = x_30;
x_7 = x_29;
x_8 = lean_box(0);
x_9 = lean_box(0);
x_18 = x_27;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_14 = l_Lean_Meta_Grind_mkENode(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_16 = l_Lean_Meta_Grind_addCongrTable(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_1);
x_18 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_updateAppMap(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_20 = l_Lean_Meta_Grind_Arith_Offset_internalize(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_22 = l_Lean_Meta_Grind_propagateUp(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Meta_Grind_propagateBetaForNewApp(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
return x_14;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_1);
x_16 = l_Lean_Meta_Grind_registerParent(x_1, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_array_get_size(x_3);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_internalize___spec__1(x_1, x_4, x_3, x_21, x_21, x_22, x_19, lean_box(0), lean_box(0), x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_10(x_5, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nestedProof", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2;
x_3 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_16; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_16 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_18 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_20 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_34; lean_object* x_69; uint8_t x_70; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_3);
x_69 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4;
x_70 = l_Lean_Expr_isConstOf(x_4, x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_box(0);
x_34 = x_71;
goto block_68;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_array_get_size(x_5);
x_73 = lean_unsigned_to_nat(2u);
x_74 = lean_nat_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_72);
x_75 = lean_box(0);
x_34 = x_75;
goto block_68;
}
else
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; 
lean_dec(x_22);
lean_dec(x_4);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_dec_lt(x_76, x_72);
lean_dec(x_72);
lean_inc(x_1);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_1);
if (x_77 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_5);
x_79 = l_Lean_instInhabitedExpr;
x_80 = l_outOfBounds___rarg(x_79);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_80);
x_81 = l_Lean_Meta_Grind_internalize(x_80, x_2, x_78, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
lean_inc(x_1);
x_83 = l_Lean_Meta_Grind_registerParent(x_1, x_80, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_84, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_85);
lean_dec(x_84);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_80);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_81);
if (x_87 == 0)
{
return x_81;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_81, 0);
x_89 = lean_ctor_get(x_81, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_81);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_array_fget(x_5, x_76);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_91);
x_92 = l_Lean_Meta_Grind_internalize(x_91, x_2, x_78, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
lean_inc(x_1);
x_94 = l_Lean_Meta_Grind_registerParent(x_1, x_91, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_95, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_96);
lean_dec(x_95);
return x_97;
}
else
{
uint8_t x_98; 
lean_dec(x_91);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_92);
if (x_98 == 0)
{
return x_92;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_92, 0);
x_100 = lean_ctor_get(x_92, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_92);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
block_33:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_23);
lean_inc(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_25 = l_Lean_Meta_Grind_internalize(x_4, x_2, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_22, x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_27);
lean_dec(x_26);
lean_dec(x_5);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
block_68:
{
lean_object* x_35; uint8_t x_36; 
lean_dec(x_34);
x_35 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2;
x_36 = l_Lean_Expr_isConstOf(x_4, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_3);
x_37 = lean_box(0);
x_23 = x_37;
goto block_33;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_array_get_size(x_5);
x_39 = lean_unsigned_to_nat(5u);
x_40 = lean_nat_dec_eq(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_3);
x_41 = lean_box(0);
x_23 = x_41;
goto block_33;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; 
lean_dec(x_22);
lean_dec(x_4);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_dec_lt(x_42, x_38);
lean_dec(x_38);
lean_inc(x_1);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_1);
if (x_43 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_5);
x_45 = l_Lean_instInhabitedExpr;
x_46 = l_outOfBounds___rarg(x_45);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_46);
x_47 = l_Lean_Meta_Grind_internalize(x_46, x_2, x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_1);
x_49 = l_Lean_Meta_Grind_registerParent(x_1, x_46, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_50, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_51);
lean_dec(x_50);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_46);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_47);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_array_fget(x_5, x_42);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_57);
x_58 = l_Lean_Meta_Grind_internalize(x_57, x_2, x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
lean_inc(x_1);
x_60 = l_Lean_Meta_Grind_registerParent(x_1, x_57, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_61, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_62);
lean_dec(x_61);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_57);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_58);
if (x_64 == 0)
{
return x_58;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_58, 0);
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_58);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_20);
if (x_102 == 0)
{
return x_20;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_20, 0);
x_104 = lean_ctor_get(x_20, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_20);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_18);
if (x_106 == 0)
{
return x_18;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_18, 0);
x_108 = lean_ctor_get(x_18, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_18);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_16);
if (x_110 == 0)
{
return x_16;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_16, 0);
x_112 = lean_ctor_get(x_16, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_16);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
case 1:
{
lean_object* x_114; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_114 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_116 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_118 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_132; lean_object* x_167; uint8_t x_168; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_120 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_120, 0, x_1);
lean_closure_set(x_120, 1, x_2);
lean_closure_set(x_120, 2, x_3);
x_167 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4;
x_168 = l_Lean_Expr_isConstOf(x_4, x_167);
if (x_168 == 0)
{
lean_object* x_169; 
x_169 = lean_box(0);
x_132 = x_169;
goto block_166;
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = lean_array_get_size(x_5);
x_171 = lean_unsigned_to_nat(2u);
x_172 = lean_nat_dec_eq(x_170, x_171);
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec(x_170);
x_173 = lean_box(0);
x_132 = x_173;
goto block_166;
}
else
{
lean_object* x_174; uint8_t x_175; lean_object* x_176; 
lean_dec(x_120);
lean_dec(x_4);
x_174 = lean_unsigned_to_nat(0u);
x_175 = lean_nat_dec_lt(x_174, x_170);
lean_dec(x_170);
lean_inc(x_1);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_1);
if (x_175 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_5);
x_177 = l_Lean_instInhabitedExpr;
x_178 = l_outOfBounds___rarg(x_177);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_178);
x_179 = l_Lean_Meta_Grind_internalize(x_178, x_2, x_176, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_119);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
lean_inc(x_1);
x_181 = l_Lean_Meta_Grind_registerParent(x_1, x_178, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_180);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_182, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_183);
lean_dec(x_182);
return x_184;
}
else
{
uint8_t x_185; 
lean_dec(x_178);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_179);
if (x_185 == 0)
{
return x_179;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_179, 0);
x_187 = lean_ctor_get(x_179, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_179);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_array_fget(x_5, x_174);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_189);
x_190 = l_Lean_Meta_Grind_internalize(x_189, x_2, x_176, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_119);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
lean_inc(x_1);
x_192 = l_Lean_Meta_Grind_registerParent(x_1, x_189, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_191);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_193, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_194);
lean_dec(x_193);
return x_195;
}
else
{
uint8_t x_196; 
lean_dec(x_189);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_190);
if (x_196 == 0)
{
return x_190;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_190, 0);
x_198 = lean_ctor_get(x_190, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_190);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
}
}
block_131:
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_121);
lean_inc(x_1);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_123 = l_Lean_Meta_Grind_internalize(x_4, x_2, x_122, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_119);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_120, x_124, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_125);
lean_dec(x_124);
lean_dec(x_5);
return x_126;
}
else
{
uint8_t x_127; 
lean_dec(x_120);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_123);
if (x_127 == 0)
{
return x_123;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_123, 0);
x_129 = lean_ctor_get(x_123, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_123);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
block_166:
{
lean_object* x_133; uint8_t x_134; 
lean_dec(x_132);
x_133 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2;
x_134 = l_Lean_Expr_isConstOf(x_4, x_133);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_3);
x_135 = lean_box(0);
x_121 = x_135;
goto block_131;
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_array_get_size(x_5);
x_137 = lean_unsigned_to_nat(5u);
x_138 = lean_nat_dec_eq(x_136, x_137);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec(x_136);
lean_dec(x_3);
x_139 = lean_box(0);
x_121 = x_139;
goto block_131;
}
else
{
lean_object* x_140; uint8_t x_141; lean_object* x_142; 
lean_dec(x_120);
lean_dec(x_4);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_dec_lt(x_140, x_136);
lean_dec(x_136);
lean_inc(x_1);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_1);
if (x_141 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_5);
x_143 = l_Lean_instInhabitedExpr;
x_144 = l_outOfBounds___rarg(x_143);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_144);
x_145 = l_Lean_Meta_Grind_internalize(x_144, x_2, x_142, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_119);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
lean_inc(x_1);
x_147 = l_Lean_Meta_Grind_registerParent(x_1, x_144, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_148, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_149);
lean_dec(x_148);
return x_150;
}
else
{
uint8_t x_151; 
lean_dec(x_144);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_145);
if (x_151 == 0)
{
return x_145;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_145, 0);
x_153 = lean_ctor_get(x_145, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_145);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_array_fget(x_5, x_140);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_155);
x_156 = l_Lean_Meta_Grind_internalize(x_155, x_2, x_142, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_119);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
lean_inc(x_1);
x_158 = l_Lean_Meta_Grind_registerParent(x_1, x_155, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_159, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_160);
lean_dec(x_159);
return x_161;
}
else
{
uint8_t x_162; 
lean_dec(x_155);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_156);
if (x_162 == 0)
{
return x_156;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_156, 0);
x_164 = lean_ctor_get(x_156, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_156);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
}
}
}
}
else
{
uint8_t x_200; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_200 = !lean_is_exclusive(x_118);
if (x_200 == 0)
{
return x_118;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_118, 0);
x_202 = lean_ctor_get(x_118, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_118);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_204 = !lean_is_exclusive(x_116);
if (x_204 == 0)
{
return x_116;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_116, 0);
x_206 = lean_ctor_get(x_116, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_116);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_114);
if (x_208 == 0)
{
return x_114;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_114, 0);
x_210 = lean_ctor_get(x_114, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_114);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
case 2:
{
lean_object* x_212; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_212 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_214 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_216 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_215);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_230; lean_object* x_265; uint8_t x_266; 
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_218 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_218, 0, x_1);
lean_closure_set(x_218, 1, x_2);
lean_closure_set(x_218, 2, x_3);
x_265 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4;
x_266 = l_Lean_Expr_isConstOf(x_4, x_265);
if (x_266 == 0)
{
lean_object* x_267; 
x_267 = lean_box(0);
x_230 = x_267;
goto block_264;
}
else
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_268 = lean_array_get_size(x_5);
x_269 = lean_unsigned_to_nat(2u);
x_270 = lean_nat_dec_eq(x_268, x_269);
if (x_270 == 0)
{
lean_object* x_271; 
lean_dec(x_268);
x_271 = lean_box(0);
x_230 = x_271;
goto block_264;
}
else
{
lean_object* x_272; uint8_t x_273; lean_object* x_274; 
lean_dec(x_218);
lean_dec(x_4);
x_272 = lean_unsigned_to_nat(0u);
x_273 = lean_nat_dec_lt(x_272, x_268);
lean_dec(x_268);
lean_inc(x_1);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_1);
if (x_273 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_5);
x_275 = l_Lean_instInhabitedExpr;
x_276 = l_outOfBounds___rarg(x_275);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_276);
x_277 = l_Lean_Meta_Grind_internalize(x_276, x_2, x_274, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_217);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec(x_277);
lean_inc(x_1);
x_279 = l_Lean_Meta_Grind_registerParent(x_1, x_276, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_278);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_280, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_281);
lean_dec(x_280);
return x_282;
}
else
{
uint8_t x_283; 
lean_dec(x_276);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_283 = !lean_is_exclusive(x_277);
if (x_283 == 0)
{
return x_277;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_277, 0);
x_285 = lean_ctor_get(x_277, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_277);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_array_fget(x_5, x_272);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_287);
x_288 = l_Lean_Meta_Grind_internalize(x_287, x_2, x_274, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_217);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
lean_dec(x_288);
lean_inc(x_1);
x_290 = l_Lean_Meta_Grind_registerParent(x_1, x_287, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_289);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_291, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_292);
lean_dec(x_291);
return x_293;
}
else
{
uint8_t x_294; 
lean_dec(x_287);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_294 = !lean_is_exclusive(x_288);
if (x_294 == 0)
{
return x_288;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_288, 0);
x_296 = lean_ctor_get(x_288, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_288);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
}
}
block_229:
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_219);
lean_inc(x_1);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_221 = l_Lean_Meta_Grind_internalize(x_4, x_2, x_220, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_217);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_218, x_222, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_223);
lean_dec(x_222);
lean_dec(x_5);
return x_224;
}
else
{
uint8_t x_225; 
lean_dec(x_218);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_225 = !lean_is_exclusive(x_221);
if (x_225 == 0)
{
return x_221;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_221, 0);
x_227 = lean_ctor_get(x_221, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_221);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
block_264:
{
lean_object* x_231; uint8_t x_232; 
lean_dec(x_230);
x_231 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2;
x_232 = l_Lean_Expr_isConstOf(x_4, x_231);
if (x_232 == 0)
{
lean_object* x_233; 
lean_dec(x_3);
x_233 = lean_box(0);
x_219 = x_233;
goto block_229;
}
else
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_234 = lean_array_get_size(x_5);
x_235 = lean_unsigned_to_nat(5u);
x_236 = lean_nat_dec_eq(x_234, x_235);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec(x_234);
lean_dec(x_3);
x_237 = lean_box(0);
x_219 = x_237;
goto block_229;
}
else
{
lean_object* x_238; uint8_t x_239; lean_object* x_240; 
lean_dec(x_218);
lean_dec(x_4);
x_238 = lean_unsigned_to_nat(1u);
x_239 = lean_nat_dec_lt(x_238, x_234);
lean_dec(x_234);
lean_inc(x_1);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_1);
if (x_239 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_5);
x_241 = l_Lean_instInhabitedExpr;
x_242 = l_outOfBounds___rarg(x_241);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_242);
x_243 = l_Lean_Meta_Grind_internalize(x_242, x_2, x_240, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_217);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
lean_inc(x_1);
x_245 = l_Lean_Meta_Grind_registerParent(x_1, x_242, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_244);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_246, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_247);
lean_dec(x_246);
return x_248;
}
else
{
uint8_t x_249; 
lean_dec(x_242);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_249 = !lean_is_exclusive(x_243);
if (x_249 == 0)
{
return x_243;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_243, 0);
x_251 = lean_ctor_get(x_243, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_243);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_array_fget(x_5, x_238);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_253);
x_254 = l_Lean_Meta_Grind_internalize(x_253, x_2, x_240, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_217);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec(x_254);
lean_inc(x_1);
x_256 = l_Lean_Meta_Grind_registerParent(x_1, x_253, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_255);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_257, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_258);
lean_dec(x_257);
return x_259;
}
else
{
uint8_t x_260; 
lean_dec(x_253);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_260 = !lean_is_exclusive(x_254);
if (x_260 == 0)
{
return x_254;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_254, 0);
x_262 = lean_ctor_get(x_254, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_254);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
}
}
}
}
else
{
uint8_t x_298; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_298 = !lean_is_exclusive(x_216);
if (x_298 == 0)
{
return x_216;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_216, 0);
x_300 = lean_ctor_get(x_216, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_216);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_214);
if (x_302 == 0)
{
return x_214;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_214, 0);
x_304 = lean_ctor_get(x_214, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_214);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_212);
if (x_306 == 0)
{
return x_212;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_212, 0);
x_308 = lean_ctor_get(x_212, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_212);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
case 3:
{
lean_object* x_310; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_310 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec(x_310);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_312 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_311);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
lean_dec(x_312);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_314 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_313);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_328; lean_object* x_363; uint8_t x_364; 
x_315 = lean_ctor_get(x_314, 1);
lean_inc(x_315);
lean_dec(x_314);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_316 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_316, 0, x_1);
lean_closure_set(x_316, 1, x_2);
lean_closure_set(x_316, 2, x_3);
x_363 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4;
x_364 = l_Lean_Expr_isConstOf(x_4, x_363);
if (x_364 == 0)
{
lean_object* x_365; 
x_365 = lean_box(0);
x_328 = x_365;
goto block_362;
}
else
{
lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_366 = lean_array_get_size(x_5);
x_367 = lean_unsigned_to_nat(2u);
x_368 = lean_nat_dec_eq(x_366, x_367);
if (x_368 == 0)
{
lean_object* x_369; 
lean_dec(x_366);
x_369 = lean_box(0);
x_328 = x_369;
goto block_362;
}
else
{
lean_object* x_370; uint8_t x_371; lean_object* x_372; 
lean_dec(x_316);
lean_dec(x_4);
x_370 = lean_unsigned_to_nat(0u);
x_371 = lean_nat_dec_lt(x_370, x_366);
lean_dec(x_366);
lean_inc(x_1);
x_372 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_372, 0, x_1);
if (x_371 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_5);
x_373 = l_Lean_instInhabitedExpr;
x_374 = l_outOfBounds___rarg(x_373);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_374);
x_375 = l_Lean_Meta_Grind_internalize(x_374, x_2, x_372, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_315);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
lean_dec(x_375);
lean_inc(x_1);
x_377 = l_Lean_Meta_Grind_registerParent(x_1, x_374, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_376);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
x_380 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_378, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_379);
lean_dec(x_378);
return x_380;
}
else
{
uint8_t x_381; 
lean_dec(x_374);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_381 = !lean_is_exclusive(x_375);
if (x_381 == 0)
{
return x_375;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_375, 0);
x_383 = lean_ctor_get(x_375, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_375);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
else
{
lean_object* x_385; lean_object* x_386; 
x_385 = lean_array_fget(x_5, x_370);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_385);
x_386 = l_Lean_Meta_Grind_internalize(x_385, x_2, x_372, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_315);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_387 = lean_ctor_get(x_386, 1);
lean_inc(x_387);
lean_dec(x_386);
lean_inc(x_1);
x_388 = l_Lean_Meta_Grind_registerParent(x_1, x_385, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_387);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_389, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_390);
lean_dec(x_389);
return x_391;
}
else
{
uint8_t x_392; 
lean_dec(x_385);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_392 = !lean_is_exclusive(x_386);
if (x_392 == 0)
{
return x_386;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_386, 0);
x_394 = lean_ctor_get(x_386, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_386);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
return x_395;
}
}
}
}
}
block_327:
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_317);
lean_inc(x_1);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_319 = l_Lean_Meta_Grind_internalize(x_4, x_2, x_318, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_315);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
x_322 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_316, x_320, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_321);
lean_dec(x_320);
lean_dec(x_5);
return x_322;
}
else
{
uint8_t x_323; 
lean_dec(x_316);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_323 = !lean_is_exclusive(x_319);
if (x_323 == 0)
{
return x_319;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_319, 0);
x_325 = lean_ctor_get(x_319, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_319);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
}
block_362:
{
lean_object* x_329; uint8_t x_330; 
lean_dec(x_328);
x_329 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2;
x_330 = l_Lean_Expr_isConstOf(x_4, x_329);
if (x_330 == 0)
{
lean_object* x_331; 
lean_dec(x_3);
x_331 = lean_box(0);
x_317 = x_331;
goto block_327;
}
else
{
lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_332 = lean_array_get_size(x_5);
x_333 = lean_unsigned_to_nat(5u);
x_334 = lean_nat_dec_eq(x_332, x_333);
if (x_334 == 0)
{
lean_object* x_335; 
lean_dec(x_332);
lean_dec(x_3);
x_335 = lean_box(0);
x_317 = x_335;
goto block_327;
}
else
{
lean_object* x_336; uint8_t x_337; lean_object* x_338; 
lean_dec(x_316);
lean_dec(x_4);
x_336 = lean_unsigned_to_nat(1u);
x_337 = lean_nat_dec_lt(x_336, x_332);
lean_dec(x_332);
lean_inc(x_1);
x_338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_338, 0, x_1);
if (x_337 == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_5);
x_339 = l_Lean_instInhabitedExpr;
x_340 = l_outOfBounds___rarg(x_339);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_340);
x_341 = l_Lean_Meta_Grind_internalize(x_340, x_2, x_338, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_315);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_342 = lean_ctor_get(x_341, 1);
lean_inc(x_342);
lean_dec(x_341);
lean_inc(x_1);
x_343 = l_Lean_Meta_Grind_registerParent(x_1, x_340, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_342);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_344, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_345);
lean_dec(x_344);
return x_346;
}
else
{
uint8_t x_347; 
lean_dec(x_340);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_347 = !lean_is_exclusive(x_341);
if (x_347 == 0)
{
return x_341;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_341, 0);
x_349 = lean_ctor_get(x_341, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_341);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
else
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_array_fget(x_5, x_336);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_351);
x_352 = l_Lean_Meta_Grind_internalize(x_351, x_2, x_338, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_315);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
lean_dec(x_352);
lean_inc(x_1);
x_354 = l_Lean_Meta_Grind_registerParent(x_1, x_351, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_353);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
x_357 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_355, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_356);
lean_dec(x_355);
return x_357;
}
else
{
uint8_t x_358; 
lean_dec(x_351);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_358 = !lean_is_exclusive(x_352);
if (x_358 == 0)
{
return x_352;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_352, 0);
x_360 = lean_ctor_get(x_352, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_352);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
return x_361;
}
}
}
}
}
}
}
else
{
uint8_t x_396; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_396 = !lean_is_exclusive(x_314);
if (x_396 == 0)
{
return x_314;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_314, 0);
x_398 = lean_ctor_get(x_314, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_314);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
return x_399;
}
}
}
else
{
uint8_t x_400; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_400 = !lean_is_exclusive(x_312);
if (x_400 == 0)
{
return x_312;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_312, 0);
x_402 = lean_ctor_get(x_312, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_312);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
}
}
else
{
uint8_t x_404; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_404 = !lean_is_exclusive(x_310);
if (x_404 == 0)
{
return x_310;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_310, 0);
x_406 = lean_ctor_get(x_310, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_310);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
return x_407;
}
}
}
case 4:
{
lean_object* x_408; lean_object* x_409; 
lean_dec(x_6);
x_408 = lean_ctor_get(x_4, 0);
lean_inc(x_408);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_409 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; 
x_410 = lean_ctor_get(x_409, 1);
lean_inc(x_410);
lean_dec(x_409);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_411 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_410);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_411, 1);
lean_inc(x_412);
lean_dec(x_411);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_413 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_412);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_426; lean_object* x_461; uint8_t x_462; 
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
lean_dec(x_413);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_415 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_415, 0, x_1);
lean_closure_set(x_415, 1, x_2);
lean_closure_set(x_415, 2, x_3);
x_461 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4;
x_462 = l_Lean_Expr_isConstOf(x_4, x_461);
if (x_462 == 0)
{
lean_object* x_463; 
x_463 = lean_box(0);
x_426 = x_463;
goto block_460;
}
else
{
lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_464 = lean_array_get_size(x_5);
x_465 = lean_unsigned_to_nat(2u);
x_466 = lean_nat_dec_eq(x_464, x_465);
if (x_466 == 0)
{
lean_object* x_467; 
lean_dec(x_464);
x_467 = lean_box(0);
x_426 = x_467;
goto block_460;
}
else
{
lean_object* x_468; uint8_t x_469; lean_object* x_470; 
lean_dec(x_415);
lean_dec(x_408);
lean_dec(x_4);
x_468 = lean_unsigned_to_nat(0u);
x_469 = lean_nat_dec_lt(x_468, x_464);
lean_dec(x_464);
lean_inc(x_1);
x_470 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_470, 0, x_1);
if (x_469 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_5);
x_471 = l_Lean_instInhabitedExpr;
x_472 = l_outOfBounds___rarg(x_471);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_472);
x_473 = l_Lean_Meta_Grind_internalize(x_472, x_2, x_470, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_414);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_474 = lean_ctor_get(x_473, 1);
lean_inc(x_474);
lean_dec(x_473);
lean_inc(x_1);
x_475 = l_Lean_Meta_Grind_registerParent(x_1, x_472, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_474);
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec(x_475);
x_478 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_476, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_477);
lean_dec(x_476);
return x_478;
}
else
{
uint8_t x_479; 
lean_dec(x_472);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_479 = !lean_is_exclusive(x_473);
if (x_479 == 0)
{
return x_473;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_473, 0);
x_481 = lean_ctor_get(x_473, 1);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_473);
x_482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set(x_482, 1, x_481);
return x_482;
}
}
}
else
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_array_fget(x_5, x_468);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_483);
x_484 = l_Lean_Meta_Grind_internalize(x_483, x_2, x_470, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_414);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_485 = lean_ctor_get(x_484, 1);
lean_inc(x_485);
lean_dec(x_484);
lean_inc(x_1);
x_486 = l_Lean_Meta_Grind_registerParent(x_1, x_483, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_485);
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
lean_dec(x_486);
x_489 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_487, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_488);
lean_dec(x_487);
return x_489;
}
else
{
uint8_t x_490; 
lean_dec(x_483);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_490 = !lean_is_exclusive(x_484);
if (x_490 == 0)
{
return x_484;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_484, 0);
x_492 = lean_ctor_get(x_484, 1);
lean_inc(x_492);
lean_inc(x_491);
lean_dec(x_484);
x_493 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_492);
return x_493;
}
}
}
}
}
block_425:
{
lean_object* x_417; 
lean_dec(x_416);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_417 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns(x_408, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_414);
lean_dec(x_408);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_415, x_418, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_419);
lean_dec(x_418);
lean_dec(x_5);
return x_420;
}
else
{
uint8_t x_421; 
lean_dec(x_415);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_421 = !lean_is_exclusive(x_417);
if (x_421 == 0)
{
return x_417;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_422 = lean_ctor_get(x_417, 0);
x_423 = lean_ctor_get(x_417, 1);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_417);
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
return x_424;
}
}
}
block_460:
{
lean_object* x_427; uint8_t x_428; 
lean_dec(x_426);
x_427 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2;
x_428 = l_Lean_Expr_isConstOf(x_4, x_427);
if (x_428 == 0)
{
lean_object* x_429; 
lean_dec(x_3);
x_429 = lean_box(0);
x_416 = x_429;
goto block_425;
}
else
{
lean_object* x_430; lean_object* x_431; uint8_t x_432; 
x_430 = lean_array_get_size(x_5);
x_431 = lean_unsigned_to_nat(5u);
x_432 = lean_nat_dec_eq(x_430, x_431);
if (x_432 == 0)
{
lean_object* x_433; 
lean_dec(x_430);
lean_dec(x_3);
x_433 = lean_box(0);
x_416 = x_433;
goto block_425;
}
else
{
lean_object* x_434; uint8_t x_435; lean_object* x_436; 
lean_dec(x_415);
lean_dec(x_408);
lean_dec(x_4);
x_434 = lean_unsigned_to_nat(1u);
x_435 = lean_nat_dec_lt(x_434, x_430);
lean_dec(x_430);
lean_inc(x_1);
x_436 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_436, 0, x_1);
if (x_435 == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_5);
x_437 = l_Lean_instInhabitedExpr;
x_438 = l_outOfBounds___rarg(x_437);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_438);
x_439 = l_Lean_Meta_Grind_internalize(x_438, x_2, x_436, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_414);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_440 = lean_ctor_get(x_439, 1);
lean_inc(x_440);
lean_dec(x_439);
lean_inc(x_1);
x_441 = l_Lean_Meta_Grind_registerParent(x_1, x_438, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_440);
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_441, 1);
lean_inc(x_443);
lean_dec(x_441);
x_444 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_442, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_443);
lean_dec(x_442);
return x_444;
}
else
{
uint8_t x_445; 
lean_dec(x_438);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_445 = !lean_is_exclusive(x_439);
if (x_445 == 0)
{
return x_439;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = lean_ctor_get(x_439, 0);
x_447 = lean_ctor_get(x_439, 1);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_439);
x_448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_448, 0, x_446);
lean_ctor_set(x_448, 1, x_447);
return x_448;
}
}
}
else
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_array_fget(x_5, x_434);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_449);
x_450 = l_Lean_Meta_Grind_internalize(x_449, x_2, x_436, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_414);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
lean_dec(x_450);
lean_inc(x_1);
x_452 = l_Lean_Meta_Grind_registerParent(x_1, x_449, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_451);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
x_455 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_453, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_454);
lean_dec(x_453);
return x_455;
}
else
{
uint8_t x_456; 
lean_dec(x_449);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_456 = !lean_is_exclusive(x_450);
if (x_456 == 0)
{
return x_450;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_450, 0);
x_458 = lean_ctor_get(x_450, 1);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_450);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
return x_459;
}
}
}
}
}
}
}
else
{
uint8_t x_494; 
lean_dec(x_408);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_494 = !lean_is_exclusive(x_413);
if (x_494 == 0)
{
return x_413;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_413, 0);
x_496 = lean_ctor_get(x_413, 1);
lean_inc(x_496);
lean_inc(x_495);
lean_dec(x_413);
x_497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_497, 0, x_495);
lean_ctor_set(x_497, 1, x_496);
return x_497;
}
}
}
else
{
uint8_t x_498; 
lean_dec(x_408);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_498 = !lean_is_exclusive(x_411);
if (x_498 == 0)
{
return x_411;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_499 = lean_ctor_get(x_411, 0);
x_500 = lean_ctor_get(x_411, 1);
lean_inc(x_500);
lean_inc(x_499);
lean_dec(x_411);
x_501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
return x_501;
}
}
}
else
{
uint8_t x_502; 
lean_dec(x_408);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_502 = !lean_is_exclusive(x_409);
if (x_502 == 0)
{
return x_409;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_409, 0);
x_504 = lean_ctor_get(x_409, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_409);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
return x_505;
}
}
}
case 5:
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_506 = lean_ctor_get(x_4, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_4, 1);
lean_inc(x_507);
lean_dec(x_4);
x_508 = lean_array_set(x_5, x_6, x_507);
x_509 = lean_unsigned_to_nat(1u);
x_510 = lean_nat_sub(x_6, x_509);
lean_dec(x_6);
x_4 = x_506;
x_5 = x_508;
x_6 = x_510;
goto _start;
}
case 6:
{
lean_object* x_512; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_512 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; 
x_513 = lean_ctor_get(x_512, 1);
lean_inc(x_513);
lean_dec(x_512);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_514 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_513);
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; lean_object* x_516; 
x_515 = lean_ctor_get(x_514, 1);
lean_inc(x_515);
lean_dec(x_514);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_516 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_515);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_530; lean_object* x_565; uint8_t x_566; 
x_517 = lean_ctor_get(x_516, 1);
lean_inc(x_517);
lean_dec(x_516);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_518 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_518, 0, x_1);
lean_closure_set(x_518, 1, x_2);
lean_closure_set(x_518, 2, x_3);
x_565 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4;
x_566 = l_Lean_Expr_isConstOf(x_4, x_565);
if (x_566 == 0)
{
lean_object* x_567; 
x_567 = lean_box(0);
x_530 = x_567;
goto block_564;
}
else
{
lean_object* x_568; lean_object* x_569; uint8_t x_570; 
x_568 = lean_array_get_size(x_5);
x_569 = lean_unsigned_to_nat(2u);
x_570 = lean_nat_dec_eq(x_568, x_569);
if (x_570 == 0)
{
lean_object* x_571; 
lean_dec(x_568);
x_571 = lean_box(0);
x_530 = x_571;
goto block_564;
}
else
{
lean_object* x_572; uint8_t x_573; lean_object* x_574; 
lean_dec(x_518);
lean_dec(x_4);
x_572 = lean_unsigned_to_nat(0u);
x_573 = lean_nat_dec_lt(x_572, x_568);
lean_dec(x_568);
lean_inc(x_1);
x_574 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_574, 0, x_1);
if (x_573 == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
lean_dec(x_5);
x_575 = l_Lean_instInhabitedExpr;
x_576 = l_outOfBounds___rarg(x_575);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_576);
x_577 = l_Lean_Meta_Grind_internalize(x_576, x_2, x_574, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_517);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_578 = lean_ctor_get(x_577, 1);
lean_inc(x_578);
lean_dec(x_577);
lean_inc(x_1);
x_579 = l_Lean_Meta_Grind_registerParent(x_1, x_576, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_578);
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
lean_dec(x_579);
x_582 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_580, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_581);
lean_dec(x_580);
return x_582;
}
else
{
uint8_t x_583; 
lean_dec(x_576);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_583 = !lean_is_exclusive(x_577);
if (x_583 == 0)
{
return x_577;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_577, 0);
x_585 = lean_ctor_get(x_577, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_577);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
return x_586;
}
}
}
else
{
lean_object* x_587; lean_object* x_588; 
x_587 = lean_array_fget(x_5, x_572);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_587);
x_588 = l_Lean_Meta_Grind_internalize(x_587, x_2, x_574, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_517);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_589 = lean_ctor_get(x_588, 1);
lean_inc(x_589);
lean_dec(x_588);
lean_inc(x_1);
x_590 = l_Lean_Meta_Grind_registerParent(x_1, x_587, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_589);
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
lean_dec(x_590);
x_593 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_591, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_592);
lean_dec(x_591);
return x_593;
}
else
{
uint8_t x_594; 
lean_dec(x_587);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_594 = !lean_is_exclusive(x_588);
if (x_594 == 0)
{
return x_588;
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_595 = lean_ctor_get(x_588, 0);
x_596 = lean_ctor_get(x_588, 1);
lean_inc(x_596);
lean_inc(x_595);
lean_dec(x_588);
x_597 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_597, 0, x_595);
lean_ctor_set(x_597, 1, x_596);
return x_597;
}
}
}
}
}
block_529:
{
lean_object* x_520; lean_object* x_521; 
lean_dec(x_519);
lean_inc(x_1);
x_520 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_520, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_521 = l_Lean_Meta_Grind_internalize(x_4, x_2, x_520, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_517);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
lean_dec(x_521);
x_524 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_518, x_522, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_523);
lean_dec(x_522);
lean_dec(x_5);
return x_524;
}
else
{
uint8_t x_525; 
lean_dec(x_518);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_525 = !lean_is_exclusive(x_521);
if (x_525 == 0)
{
return x_521;
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_526 = lean_ctor_get(x_521, 0);
x_527 = lean_ctor_get(x_521, 1);
lean_inc(x_527);
lean_inc(x_526);
lean_dec(x_521);
x_528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_528, 0, x_526);
lean_ctor_set(x_528, 1, x_527);
return x_528;
}
}
}
block_564:
{
lean_object* x_531; uint8_t x_532; 
lean_dec(x_530);
x_531 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2;
x_532 = l_Lean_Expr_isConstOf(x_4, x_531);
if (x_532 == 0)
{
lean_object* x_533; 
lean_dec(x_3);
x_533 = lean_box(0);
x_519 = x_533;
goto block_529;
}
else
{
lean_object* x_534; lean_object* x_535; uint8_t x_536; 
x_534 = lean_array_get_size(x_5);
x_535 = lean_unsigned_to_nat(5u);
x_536 = lean_nat_dec_eq(x_534, x_535);
if (x_536 == 0)
{
lean_object* x_537; 
lean_dec(x_534);
lean_dec(x_3);
x_537 = lean_box(0);
x_519 = x_537;
goto block_529;
}
else
{
lean_object* x_538; uint8_t x_539; lean_object* x_540; 
lean_dec(x_518);
lean_dec(x_4);
x_538 = lean_unsigned_to_nat(1u);
x_539 = lean_nat_dec_lt(x_538, x_534);
lean_dec(x_534);
lean_inc(x_1);
x_540 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_540, 0, x_1);
if (x_539 == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_5);
x_541 = l_Lean_instInhabitedExpr;
x_542 = l_outOfBounds___rarg(x_541);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_542);
x_543 = l_Lean_Meta_Grind_internalize(x_542, x_2, x_540, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_517);
if (lean_obj_tag(x_543) == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_544 = lean_ctor_get(x_543, 1);
lean_inc(x_544);
lean_dec(x_543);
lean_inc(x_1);
x_545 = l_Lean_Meta_Grind_registerParent(x_1, x_542, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_544);
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
lean_dec(x_545);
x_548 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_546, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_547);
lean_dec(x_546);
return x_548;
}
else
{
uint8_t x_549; 
lean_dec(x_542);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_549 = !lean_is_exclusive(x_543);
if (x_549 == 0)
{
return x_543;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_543, 0);
x_551 = lean_ctor_get(x_543, 1);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_543);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
}
else
{
lean_object* x_553; lean_object* x_554; 
x_553 = lean_array_fget(x_5, x_538);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_553);
x_554 = l_Lean_Meta_Grind_internalize(x_553, x_2, x_540, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_517);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_555 = lean_ctor_get(x_554, 1);
lean_inc(x_555);
lean_dec(x_554);
lean_inc(x_1);
x_556 = l_Lean_Meta_Grind_registerParent(x_1, x_553, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_555);
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
lean_dec(x_556);
x_559 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_557, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_558);
lean_dec(x_557);
return x_559;
}
else
{
uint8_t x_560; 
lean_dec(x_553);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_560 = !lean_is_exclusive(x_554);
if (x_560 == 0)
{
return x_554;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_561 = lean_ctor_get(x_554, 0);
x_562 = lean_ctor_get(x_554, 1);
lean_inc(x_562);
lean_inc(x_561);
lean_dec(x_554);
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
return x_563;
}
}
}
}
}
}
}
else
{
uint8_t x_598; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_598 = !lean_is_exclusive(x_516);
if (x_598 == 0)
{
return x_516;
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_599 = lean_ctor_get(x_516, 0);
x_600 = lean_ctor_get(x_516, 1);
lean_inc(x_600);
lean_inc(x_599);
lean_dec(x_516);
x_601 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_601, 0, x_599);
lean_ctor_set(x_601, 1, x_600);
return x_601;
}
}
}
else
{
uint8_t x_602; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_602 = !lean_is_exclusive(x_514);
if (x_602 == 0)
{
return x_514;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_603 = lean_ctor_get(x_514, 0);
x_604 = lean_ctor_get(x_514, 1);
lean_inc(x_604);
lean_inc(x_603);
lean_dec(x_514);
x_605 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_605, 0, x_603);
lean_ctor_set(x_605, 1, x_604);
return x_605;
}
}
}
else
{
uint8_t x_606; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_606 = !lean_is_exclusive(x_512);
if (x_606 == 0)
{
return x_512;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = lean_ctor_get(x_512, 0);
x_608 = lean_ctor_get(x_512, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_512);
x_609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_609, 0, x_607);
lean_ctor_set(x_609, 1, x_608);
return x_609;
}
}
}
case 7:
{
lean_object* x_610; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_610 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; lean_object* x_612; 
x_611 = lean_ctor_get(x_610, 1);
lean_inc(x_611);
lean_dec(x_610);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_612 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_611);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; 
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
lean_dec(x_612);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_614 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_613);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_628; lean_object* x_663; uint8_t x_664; 
x_615 = lean_ctor_get(x_614, 1);
lean_inc(x_615);
lean_dec(x_614);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_616 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_616, 0, x_1);
lean_closure_set(x_616, 1, x_2);
lean_closure_set(x_616, 2, x_3);
x_663 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4;
x_664 = l_Lean_Expr_isConstOf(x_4, x_663);
if (x_664 == 0)
{
lean_object* x_665; 
x_665 = lean_box(0);
x_628 = x_665;
goto block_662;
}
else
{
lean_object* x_666; lean_object* x_667; uint8_t x_668; 
x_666 = lean_array_get_size(x_5);
x_667 = lean_unsigned_to_nat(2u);
x_668 = lean_nat_dec_eq(x_666, x_667);
if (x_668 == 0)
{
lean_object* x_669; 
lean_dec(x_666);
x_669 = lean_box(0);
x_628 = x_669;
goto block_662;
}
else
{
lean_object* x_670; uint8_t x_671; lean_object* x_672; 
lean_dec(x_616);
lean_dec(x_4);
x_670 = lean_unsigned_to_nat(0u);
x_671 = lean_nat_dec_lt(x_670, x_666);
lean_dec(x_666);
lean_inc(x_1);
x_672 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_672, 0, x_1);
if (x_671 == 0)
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_5);
x_673 = l_Lean_instInhabitedExpr;
x_674 = l_outOfBounds___rarg(x_673);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_674);
x_675 = l_Lean_Meta_Grind_internalize(x_674, x_2, x_672, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_615);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_676 = lean_ctor_get(x_675, 1);
lean_inc(x_676);
lean_dec(x_675);
lean_inc(x_1);
x_677 = l_Lean_Meta_Grind_registerParent(x_1, x_674, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_676);
x_678 = lean_ctor_get(x_677, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_677, 1);
lean_inc(x_679);
lean_dec(x_677);
x_680 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_678, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_679);
lean_dec(x_678);
return x_680;
}
else
{
uint8_t x_681; 
lean_dec(x_674);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_681 = !lean_is_exclusive(x_675);
if (x_681 == 0)
{
return x_675;
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_682 = lean_ctor_get(x_675, 0);
x_683 = lean_ctor_get(x_675, 1);
lean_inc(x_683);
lean_inc(x_682);
lean_dec(x_675);
x_684 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_684, 0, x_682);
lean_ctor_set(x_684, 1, x_683);
return x_684;
}
}
}
else
{
lean_object* x_685; lean_object* x_686; 
x_685 = lean_array_fget(x_5, x_670);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_685);
x_686 = l_Lean_Meta_Grind_internalize(x_685, x_2, x_672, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_615);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_687 = lean_ctor_get(x_686, 1);
lean_inc(x_687);
lean_dec(x_686);
lean_inc(x_1);
x_688 = l_Lean_Meta_Grind_registerParent(x_1, x_685, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_687);
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
lean_dec(x_688);
x_691 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_689, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_690);
lean_dec(x_689);
return x_691;
}
else
{
uint8_t x_692; 
lean_dec(x_685);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_692 = !lean_is_exclusive(x_686);
if (x_692 == 0)
{
return x_686;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_693 = lean_ctor_get(x_686, 0);
x_694 = lean_ctor_get(x_686, 1);
lean_inc(x_694);
lean_inc(x_693);
lean_dec(x_686);
x_695 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_695, 0, x_693);
lean_ctor_set(x_695, 1, x_694);
return x_695;
}
}
}
}
}
block_627:
{
lean_object* x_618; lean_object* x_619; 
lean_dec(x_617);
lean_inc(x_1);
x_618 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_618, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_619 = l_Lean_Meta_Grind_internalize(x_4, x_2, x_618, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_615);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
lean_dec(x_619);
x_622 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_616, x_620, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_621);
lean_dec(x_620);
lean_dec(x_5);
return x_622;
}
else
{
uint8_t x_623; 
lean_dec(x_616);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_623 = !lean_is_exclusive(x_619);
if (x_623 == 0)
{
return x_619;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_624 = lean_ctor_get(x_619, 0);
x_625 = lean_ctor_get(x_619, 1);
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_619);
x_626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_626, 0, x_624);
lean_ctor_set(x_626, 1, x_625);
return x_626;
}
}
}
block_662:
{
lean_object* x_629; uint8_t x_630; 
lean_dec(x_628);
x_629 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2;
x_630 = l_Lean_Expr_isConstOf(x_4, x_629);
if (x_630 == 0)
{
lean_object* x_631; 
lean_dec(x_3);
x_631 = lean_box(0);
x_617 = x_631;
goto block_627;
}
else
{
lean_object* x_632; lean_object* x_633; uint8_t x_634; 
x_632 = lean_array_get_size(x_5);
x_633 = lean_unsigned_to_nat(5u);
x_634 = lean_nat_dec_eq(x_632, x_633);
if (x_634 == 0)
{
lean_object* x_635; 
lean_dec(x_632);
lean_dec(x_3);
x_635 = lean_box(0);
x_617 = x_635;
goto block_627;
}
else
{
lean_object* x_636; uint8_t x_637; lean_object* x_638; 
lean_dec(x_616);
lean_dec(x_4);
x_636 = lean_unsigned_to_nat(1u);
x_637 = lean_nat_dec_lt(x_636, x_632);
lean_dec(x_632);
lean_inc(x_1);
x_638 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_638, 0, x_1);
if (x_637 == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; 
lean_dec(x_5);
x_639 = l_Lean_instInhabitedExpr;
x_640 = l_outOfBounds___rarg(x_639);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_640);
x_641 = l_Lean_Meta_Grind_internalize(x_640, x_2, x_638, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_615);
if (lean_obj_tag(x_641) == 0)
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_642 = lean_ctor_get(x_641, 1);
lean_inc(x_642);
lean_dec(x_641);
lean_inc(x_1);
x_643 = l_Lean_Meta_Grind_registerParent(x_1, x_640, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_642);
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_643, 1);
lean_inc(x_645);
lean_dec(x_643);
x_646 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_644, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_645);
lean_dec(x_644);
return x_646;
}
else
{
uint8_t x_647; 
lean_dec(x_640);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_647 = !lean_is_exclusive(x_641);
if (x_647 == 0)
{
return x_641;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_641, 0);
x_649 = lean_ctor_get(x_641, 1);
lean_inc(x_649);
lean_inc(x_648);
lean_dec(x_641);
x_650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_649);
return x_650;
}
}
}
else
{
lean_object* x_651; lean_object* x_652; 
x_651 = lean_array_fget(x_5, x_636);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_651);
x_652 = l_Lean_Meta_Grind_internalize(x_651, x_2, x_638, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_615);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_653 = lean_ctor_get(x_652, 1);
lean_inc(x_653);
lean_dec(x_652);
lean_inc(x_1);
x_654 = l_Lean_Meta_Grind_registerParent(x_1, x_651, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_653);
x_655 = lean_ctor_get(x_654, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_654, 1);
lean_inc(x_656);
lean_dec(x_654);
x_657 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_655, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_656);
lean_dec(x_655);
return x_657;
}
else
{
uint8_t x_658; 
lean_dec(x_651);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_658 = !lean_is_exclusive(x_652);
if (x_658 == 0)
{
return x_652;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_652, 0);
x_660 = lean_ctor_get(x_652, 1);
lean_inc(x_660);
lean_inc(x_659);
lean_dec(x_652);
x_661 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
return x_661;
}
}
}
}
}
}
}
else
{
uint8_t x_696; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_696 = !lean_is_exclusive(x_614);
if (x_696 == 0)
{
return x_614;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_697 = lean_ctor_get(x_614, 0);
x_698 = lean_ctor_get(x_614, 1);
lean_inc(x_698);
lean_inc(x_697);
lean_dec(x_614);
x_699 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_699, 0, x_697);
lean_ctor_set(x_699, 1, x_698);
return x_699;
}
}
}
else
{
uint8_t x_700; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_700 = !lean_is_exclusive(x_612);
if (x_700 == 0)
{
return x_612;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_701 = lean_ctor_get(x_612, 0);
x_702 = lean_ctor_get(x_612, 1);
lean_inc(x_702);
lean_inc(x_701);
lean_dec(x_612);
x_703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_703, 0, x_701);
lean_ctor_set(x_703, 1, x_702);
return x_703;
}
}
}
else
{
uint8_t x_704; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_704 = !lean_is_exclusive(x_610);
if (x_704 == 0)
{
return x_610;
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_705 = lean_ctor_get(x_610, 0);
x_706 = lean_ctor_get(x_610, 1);
lean_inc(x_706);
lean_inc(x_705);
lean_dec(x_610);
x_707 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_707, 0, x_705);
lean_ctor_set(x_707, 1, x_706);
return x_707;
}
}
}
case 8:
{
lean_object* x_708; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_708 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; lean_object* x_710; 
x_709 = lean_ctor_get(x_708, 1);
lean_inc(x_709);
lean_dec(x_708);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_710 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_709);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_711; lean_object* x_712; 
x_711 = lean_ctor_get(x_710, 1);
lean_inc(x_711);
lean_dec(x_710);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_712 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_711);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_726; lean_object* x_761; uint8_t x_762; 
x_713 = lean_ctor_get(x_712, 1);
lean_inc(x_713);
lean_dec(x_712);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_714 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_714, 0, x_1);
lean_closure_set(x_714, 1, x_2);
lean_closure_set(x_714, 2, x_3);
x_761 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4;
x_762 = l_Lean_Expr_isConstOf(x_4, x_761);
if (x_762 == 0)
{
lean_object* x_763; 
x_763 = lean_box(0);
x_726 = x_763;
goto block_760;
}
else
{
lean_object* x_764; lean_object* x_765; uint8_t x_766; 
x_764 = lean_array_get_size(x_5);
x_765 = lean_unsigned_to_nat(2u);
x_766 = lean_nat_dec_eq(x_764, x_765);
if (x_766 == 0)
{
lean_object* x_767; 
lean_dec(x_764);
x_767 = lean_box(0);
x_726 = x_767;
goto block_760;
}
else
{
lean_object* x_768; uint8_t x_769; lean_object* x_770; 
lean_dec(x_714);
lean_dec(x_4);
x_768 = lean_unsigned_to_nat(0u);
x_769 = lean_nat_dec_lt(x_768, x_764);
lean_dec(x_764);
lean_inc(x_1);
x_770 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_770, 0, x_1);
if (x_769 == 0)
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
lean_dec(x_5);
x_771 = l_Lean_instInhabitedExpr;
x_772 = l_outOfBounds___rarg(x_771);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_772);
x_773 = l_Lean_Meta_Grind_internalize(x_772, x_2, x_770, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_713);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_774 = lean_ctor_get(x_773, 1);
lean_inc(x_774);
lean_dec(x_773);
lean_inc(x_1);
x_775 = l_Lean_Meta_Grind_registerParent(x_1, x_772, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_774);
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
lean_dec(x_775);
x_778 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_776, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_777);
lean_dec(x_776);
return x_778;
}
else
{
uint8_t x_779; 
lean_dec(x_772);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_779 = !lean_is_exclusive(x_773);
if (x_779 == 0)
{
return x_773;
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_780 = lean_ctor_get(x_773, 0);
x_781 = lean_ctor_get(x_773, 1);
lean_inc(x_781);
lean_inc(x_780);
lean_dec(x_773);
x_782 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_782, 0, x_780);
lean_ctor_set(x_782, 1, x_781);
return x_782;
}
}
}
else
{
lean_object* x_783; lean_object* x_784; 
x_783 = lean_array_fget(x_5, x_768);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_783);
x_784 = l_Lean_Meta_Grind_internalize(x_783, x_2, x_770, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_713);
if (lean_obj_tag(x_784) == 0)
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_785 = lean_ctor_get(x_784, 1);
lean_inc(x_785);
lean_dec(x_784);
lean_inc(x_1);
x_786 = l_Lean_Meta_Grind_registerParent(x_1, x_783, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_785);
x_787 = lean_ctor_get(x_786, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
lean_dec(x_786);
x_789 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_787, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_788);
lean_dec(x_787);
return x_789;
}
else
{
uint8_t x_790; 
lean_dec(x_783);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_790 = !lean_is_exclusive(x_784);
if (x_790 == 0)
{
return x_784;
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_791 = lean_ctor_get(x_784, 0);
x_792 = lean_ctor_get(x_784, 1);
lean_inc(x_792);
lean_inc(x_791);
lean_dec(x_784);
x_793 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_793, 0, x_791);
lean_ctor_set(x_793, 1, x_792);
return x_793;
}
}
}
}
}
block_725:
{
lean_object* x_716; lean_object* x_717; 
lean_dec(x_715);
lean_inc(x_1);
x_716 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_716, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_717 = l_Lean_Meta_Grind_internalize(x_4, x_2, x_716, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_713);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
lean_dec(x_717);
x_720 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_714, x_718, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_719);
lean_dec(x_718);
lean_dec(x_5);
return x_720;
}
else
{
uint8_t x_721; 
lean_dec(x_714);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_721 = !lean_is_exclusive(x_717);
if (x_721 == 0)
{
return x_717;
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_722 = lean_ctor_get(x_717, 0);
x_723 = lean_ctor_get(x_717, 1);
lean_inc(x_723);
lean_inc(x_722);
lean_dec(x_717);
x_724 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_724, 0, x_722);
lean_ctor_set(x_724, 1, x_723);
return x_724;
}
}
}
block_760:
{
lean_object* x_727; uint8_t x_728; 
lean_dec(x_726);
x_727 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2;
x_728 = l_Lean_Expr_isConstOf(x_4, x_727);
if (x_728 == 0)
{
lean_object* x_729; 
lean_dec(x_3);
x_729 = lean_box(0);
x_715 = x_729;
goto block_725;
}
else
{
lean_object* x_730; lean_object* x_731; uint8_t x_732; 
x_730 = lean_array_get_size(x_5);
x_731 = lean_unsigned_to_nat(5u);
x_732 = lean_nat_dec_eq(x_730, x_731);
if (x_732 == 0)
{
lean_object* x_733; 
lean_dec(x_730);
lean_dec(x_3);
x_733 = lean_box(0);
x_715 = x_733;
goto block_725;
}
else
{
lean_object* x_734; uint8_t x_735; lean_object* x_736; 
lean_dec(x_714);
lean_dec(x_4);
x_734 = lean_unsigned_to_nat(1u);
x_735 = lean_nat_dec_lt(x_734, x_730);
lean_dec(x_730);
lean_inc(x_1);
x_736 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_736, 0, x_1);
if (x_735 == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; 
lean_dec(x_5);
x_737 = l_Lean_instInhabitedExpr;
x_738 = l_outOfBounds___rarg(x_737);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_738);
x_739 = l_Lean_Meta_Grind_internalize(x_738, x_2, x_736, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_713);
if (lean_obj_tag(x_739) == 0)
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_740 = lean_ctor_get(x_739, 1);
lean_inc(x_740);
lean_dec(x_739);
lean_inc(x_1);
x_741 = l_Lean_Meta_Grind_registerParent(x_1, x_738, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_740);
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_741, 1);
lean_inc(x_743);
lean_dec(x_741);
x_744 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_742, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_743);
lean_dec(x_742);
return x_744;
}
else
{
uint8_t x_745; 
lean_dec(x_738);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_745 = !lean_is_exclusive(x_739);
if (x_745 == 0)
{
return x_739;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_746 = lean_ctor_get(x_739, 0);
x_747 = lean_ctor_get(x_739, 1);
lean_inc(x_747);
lean_inc(x_746);
lean_dec(x_739);
x_748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
return x_748;
}
}
}
else
{
lean_object* x_749; lean_object* x_750; 
x_749 = lean_array_fget(x_5, x_734);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_749);
x_750 = l_Lean_Meta_Grind_internalize(x_749, x_2, x_736, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_713);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_751 = lean_ctor_get(x_750, 1);
lean_inc(x_751);
lean_dec(x_750);
lean_inc(x_1);
x_752 = l_Lean_Meta_Grind_registerParent(x_1, x_749, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_751);
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_752, 1);
lean_inc(x_754);
lean_dec(x_752);
x_755 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_753, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_754);
lean_dec(x_753);
return x_755;
}
else
{
uint8_t x_756; 
lean_dec(x_749);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_756 = !lean_is_exclusive(x_750);
if (x_756 == 0)
{
return x_750;
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_757 = lean_ctor_get(x_750, 0);
x_758 = lean_ctor_get(x_750, 1);
lean_inc(x_758);
lean_inc(x_757);
lean_dec(x_750);
x_759 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_759, 0, x_757);
lean_ctor_set(x_759, 1, x_758);
return x_759;
}
}
}
}
}
}
}
else
{
uint8_t x_794; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_794 = !lean_is_exclusive(x_712);
if (x_794 == 0)
{
return x_712;
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_795 = lean_ctor_get(x_712, 0);
x_796 = lean_ctor_get(x_712, 1);
lean_inc(x_796);
lean_inc(x_795);
lean_dec(x_712);
x_797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_797, 0, x_795);
lean_ctor_set(x_797, 1, x_796);
return x_797;
}
}
}
else
{
uint8_t x_798; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_798 = !lean_is_exclusive(x_710);
if (x_798 == 0)
{
return x_710;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_799 = lean_ctor_get(x_710, 0);
x_800 = lean_ctor_get(x_710, 1);
lean_inc(x_800);
lean_inc(x_799);
lean_dec(x_710);
x_801 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_801, 0, x_799);
lean_ctor_set(x_801, 1, x_800);
return x_801;
}
}
}
else
{
uint8_t x_802; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_802 = !lean_is_exclusive(x_708);
if (x_802 == 0)
{
return x_708;
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_803 = lean_ctor_get(x_708, 0);
x_804 = lean_ctor_get(x_708, 1);
lean_inc(x_804);
lean_inc(x_803);
lean_dec(x_708);
x_805 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_805, 0, x_803);
lean_ctor_set(x_805, 1, x_804);
return x_805;
}
}
}
case 9:
{
lean_object* x_806; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_806 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_806) == 0)
{
lean_object* x_807; lean_object* x_808; 
x_807 = lean_ctor_get(x_806, 1);
lean_inc(x_807);
lean_dec(x_806);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_808 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_807);
if (lean_obj_tag(x_808) == 0)
{
lean_object* x_809; lean_object* x_810; 
x_809 = lean_ctor_get(x_808, 1);
lean_inc(x_809);
lean_dec(x_808);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_810 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_809);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_824; lean_object* x_859; uint8_t x_860; 
x_811 = lean_ctor_get(x_810, 1);
lean_inc(x_811);
lean_dec(x_810);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_812 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_812, 0, x_1);
lean_closure_set(x_812, 1, x_2);
lean_closure_set(x_812, 2, x_3);
x_859 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4;
x_860 = l_Lean_Expr_isConstOf(x_4, x_859);
if (x_860 == 0)
{
lean_object* x_861; 
x_861 = lean_box(0);
x_824 = x_861;
goto block_858;
}
else
{
lean_object* x_862; lean_object* x_863; uint8_t x_864; 
x_862 = lean_array_get_size(x_5);
x_863 = lean_unsigned_to_nat(2u);
x_864 = lean_nat_dec_eq(x_862, x_863);
if (x_864 == 0)
{
lean_object* x_865; 
lean_dec(x_862);
x_865 = lean_box(0);
x_824 = x_865;
goto block_858;
}
else
{
lean_object* x_866; uint8_t x_867; lean_object* x_868; 
lean_dec(x_812);
lean_dec(x_4);
x_866 = lean_unsigned_to_nat(0u);
x_867 = lean_nat_dec_lt(x_866, x_862);
lean_dec(x_862);
lean_inc(x_1);
x_868 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_868, 0, x_1);
if (x_867 == 0)
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; 
lean_dec(x_5);
x_869 = l_Lean_instInhabitedExpr;
x_870 = l_outOfBounds___rarg(x_869);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_870);
x_871 = l_Lean_Meta_Grind_internalize(x_870, x_2, x_868, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_811);
if (lean_obj_tag(x_871) == 0)
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
x_872 = lean_ctor_get(x_871, 1);
lean_inc(x_872);
lean_dec(x_871);
lean_inc(x_1);
x_873 = l_Lean_Meta_Grind_registerParent(x_1, x_870, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_872);
x_874 = lean_ctor_get(x_873, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_873, 1);
lean_inc(x_875);
lean_dec(x_873);
x_876 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_874, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_875);
lean_dec(x_874);
return x_876;
}
else
{
uint8_t x_877; 
lean_dec(x_870);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_877 = !lean_is_exclusive(x_871);
if (x_877 == 0)
{
return x_871;
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_878 = lean_ctor_get(x_871, 0);
x_879 = lean_ctor_get(x_871, 1);
lean_inc(x_879);
lean_inc(x_878);
lean_dec(x_871);
x_880 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_880, 0, x_878);
lean_ctor_set(x_880, 1, x_879);
return x_880;
}
}
}
else
{
lean_object* x_881; lean_object* x_882; 
x_881 = lean_array_fget(x_5, x_866);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_881);
x_882 = l_Lean_Meta_Grind_internalize(x_881, x_2, x_868, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_811);
if (lean_obj_tag(x_882) == 0)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; 
x_883 = lean_ctor_get(x_882, 1);
lean_inc(x_883);
lean_dec(x_882);
lean_inc(x_1);
x_884 = l_Lean_Meta_Grind_registerParent(x_1, x_881, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_883);
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
lean_dec(x_884);
x_887 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_885, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_886);
lean_dec(x_885);
return x_887;
}
else
{
uint8_t x_888; 
lean_dec(x_881);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_888 = !lean_is_exclusive(x_882);
if (x_888 == 0)
{
return x_882;
}
else
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; 
x_889 = lean_ctor_get(x_882, 0);
x_890 = lean_ctor_get(x_882, 1);
lean_inc(x_890);
lean_inc(x_889);
lean_dec(x_882);
x_891 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_891, 0, x_889);
lean_ctor_set(x_891, 1, x_890);
return x_891;
}
}
}
}
}
block_823:
{
lean_object* x_814; lean_object* x_815; 
lean_dec(x_813);
lean_inc(x_1);
x_814 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_814, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_815 = l_Lean_Meta_Grind_internalize(x_4, x_2, x_814, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_811);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_815, 1);
lean_inc(x_817);
lean_dec(x_815);
x_818 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_812, x_816, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_817);
lean_dec(x_816);
lean_dec(x_5);
return x_818;
}
else
{
uint8_t x_819; 
lean_dec(x_812);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_819 = !lean_is_exclusive(x_815);
if (x_819 == 0)
{
return x_815;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_820 = lean_ctor_get(x_815, 0);
x_821 = lean_ctor_get(x_815, 1);
lean_inc(x_821);
lean_inc(x_820);
lean_dec(x_815);
x_822 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_822, 0, x_820);
lean_ctor_set(x_822, 1, x_821);
return x_822;
}
}
}
block_858:
{
lean_object* x_825; uint8_t x_826; 
lean_dec(x_824);
x_825 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2;
x_826 = l_Lean_Expr_isConstOf(x_4, x_825);
if (x_826 == 0)
{
lean_object* x_827; 
lean_dec(x_3);
x_827 = lean_box(0);
x_813 = x_827;
goto block_823;
}
else
{
lean_object* x_828; lean_object* x_829; uint8_t x_830; 
x_828 = lean_array_get_size(x_5);
x_829 = lean_unsigned_to_nat(5u);
x_830 = lean_nat_dec_eq(x_828, x_829);
if (x_830 == 0)
{
lean_object* x_831; 
lean_dec(x_828);
lean_dec(x_3);
x_831 = lean_box(0);
x_813 = x_831;
goto block_823;
}
else
{
lean_object* x_832; uint8_t x_833; lean_object* x_834; 
lean_dec(x_812);
lean_dec(x_4);
x_832 = lean_unsigned_to_nat(1u);
x_833 = lean_nat_dec_lt(x_832, x_828);
lean_dec(x_828);
lean_inc(x_1);
x_834 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_834, 0, x_1);
if (x_833 == 0)
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; 
lean_dec(x_5);
x_835 = l_Lean_instInhabitedExpr;
x_836 = l_outOfBounds___rarg(x_835);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_836);
x_837 = l_Lean_Meta_Grind_internalize(x_836, x_2, x_834, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_811);
if (lean_obj_tag(x_837) == 0)
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
x_838 = lean_ctor_get(x_837, 1);
lean_inc(x_838);
lean_dec(x_837);
lean_inc(x_1);
x_839 = l_Lean_Meta_Grind_registerParent(x_1, x_836, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_838);
x_840 = lean_ctor_get(x_839, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_839, 1);
lean_inc(x_841);
lean_dec(x_839);
x_842 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_840, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_841);
lean_dec(x_840);
return x_842;
}
else
{
uint8_t x_843; 
lean_dec(x_836);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_843 = !lean_is_exclusive(x_837);
if (x_843 == 0)
{
return x_837;
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; 
x_844 = lean_ctor_get(x_837, 0);
x_845 = lean_ctor_get(x_837, 1);
lean_inc(x_845);
lean_inc(x_844);
lean_dec(x_837);
x_846 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_846, 0, x_844);
lean_ctor_set(x_846, 1, x_845);
return x_846;
}
}
}
else
{
lean_object* x_847; lean_object* x_848; 
x_847 = lean_array_fget(x_5, x_832);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_847);
x_848 = l_Lean_Meta_Grind_internalize(x_847, x_2, x_834, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_811);
if (lean_obj_tag(x_848) == 0)
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; 
x_849 = lean_ctor_get(x_848, 1);
lean_inc(x_849);
lean_dec(x_848);
lean_inc(x_1);
x_850 = l_Lean_Meta_Grind_registerParent(x_1, x_847, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_849);
x_851 = lean_ctor_get(x_850, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_850, 1);
lean_inc(x_852);
lean_dec(x_850);
x_853 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_851, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_852);
lean_dec(x_851);
return x_853;
}
else
{
uint8_t x_854; 
lean_dec(x_847);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_854 = !lean_is_exclusive(x_848);
if (x_854 == 0)
{
return x_848;
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; 
x_855 = lean_ctor_get(x_848, 0);
x_856 = lean_ctor_get(x_848, 1);
lean_inc(x_856);
lean_inc(x_855);
lean_dec(x_848);
x_857 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_857, 0, x_855);
lean_ctor_set(x_857, 1, x_856);
return x_857;
}
}
}
}
}
}
}
else
{
uint8_t x_892; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_892 = !lean_is_exclusive(x_810);
if (x_892 == 0)
{
return x_810;
}
else
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; 
x_893 = lean_ctor_get(x_810, 0);
x_894 = lean_ctor_get(x_810, 1);
lean_inc(x_894);
lean_inc(x_893);
lean_dec(x_810);
x_895 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_895, 0, x_893);
lean_ctor_set(x_895, 1, x_894);
return x_895;
}
}
}
else
{
uint8_t x_896; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_896 = !lean_is_exclusive(x_808);
if (x_896 == 0)
{
return x_808;
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; 
x_897 = lean_ctor_get(x_808, 0);
x_898 = lean_ctor_get(x_808, 1);
lean_inc(x_898);
lean_inc(x_897);
lean_dec(x_808);
x_899 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_899, 0, x_897);
lean_ctor_set(x_899, 1, x_898);
return x_899;
}
}
}
else
{
uint8_t x_900; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_900 = !lean_is_exclusive(x_806);
if (x_900 == 0)
{
return x_806;
}
else
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; 
x_901 = lean_ctor_get(x_806, 0);
x_902 = lean_ctor_get(x_806, 1);
lean_inc(x_902);
lean_inc(x_901);
lean_dec(x_806);
x_903 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_903, 0, x_901);
lean_ctor_set(x_903, 1, x_902);
return x_903;
}
}
}
case 10:
{
lean_object* x_904; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_904 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_904) == 0)
{
lean_object* x_905; lean_object* x_906; 
x_905 = lean_ctor_get(x_904, 1);
lean_inc(x_905);
lean_dec(x_904);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_906 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_905);
if (lean_obj_tag(x_906) == 0)
{
lean_object* x_907; lean_object* x_908; 
x_907 = lean_ctor_get(x_906, 1);
lean_inc(x_907);
lean_dec(x_906);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_908 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_907);
if (lean_obj_tag(x_908) == 0)
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_922; lean_object* x_957; uint8_t x_958; 
x_909 = lean_ctor_get(x_908, 1);
lean_inc(x_909);
lean_dec(x_908);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_910 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_910, 0, x_1);
lean_closure_set(x_910, 1, x_2);
lean_closure_set(x_910, 2, x_3);
x_957 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4;
x_958 = l_Lean_Expr_isConstOf(x_4, x_957);
if (x_958 == 0)
{
lean_object* x_959; 
x_959 = lean_box(0);
x_922 = x_959;
goto block_956;
}
else
{
lean_object* x_960; lean_object* x_961; uint8_t x_962; 
x_960 = lean_array_get_size(x_5);
x_961 = lean_unsigned_to_nat(2u);
x_962 = lean_nat_dec_eq(x_960, x_961);
if (x_962 == 0)
{
lean_object* x_963; 
lean_dec(x_960);
x_963 = lean_box(0);
x_922 = x_963;
goto block_956;
}
else
{
lean_object* x_964; uint8_t x_965; lean_object* x_966; 
lean_dec(x_910);
lean_dec(x_4);
x_964 = lean_unsigned_to_nat(0u);
x_965 = lean_nat_dec_lt(x_964, x_960);
lean_dec(x_960);
lean_inc(x_1);
x_966 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_966, 0, x_1);
if (x_965 == 0)
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; 
lean_dec(x_5);
x_967 = l_Lean_instInhabitedExpr;
x_968 = l_outOfBounds___rarg(x_967);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_968);
x_969 = l_Lean_Meta_Grind_internalize(x_968, x_2, x_966, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_909);
if (lean_obj_tag(x_969) == 0)
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
x_970 = lean_ctor_get(x_969, 1);
lean_inc(x_970);
lean_dec(x_969);
lean_inc(x_1);
x_971 = l_Lean_Meta_Grind_registerParent(x_1, x_968, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_970);
x_972 = lean_ctor_get(x_971, 0);
lean_inc(x_972);
x_973 = lean_ctor_get(x_971, 1);
lean_inc(x_973);
lean_dec(x_971);
x_974 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_972, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_973);
lean_dec(x_972);
return x_974;
}
else
{
uint8_t x_975; 
lean_dec(x_968);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_975 = !lean_is_exclusive(x_969);
if (x_975 == 0)
{
return x_969;
}
else
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; 
x_976 = lean_ctor_get(x_969, 0);
x_977 = lean_ctor_get(x_969, 1);
lean_inc(x_977);
lean_inc(x_976);
lean_dec(x_969);
x_978 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_978, 0, x_976);
lean_ctor_set(x_978, 1, x_977);
return x_978;
}
}
}
else
{
lean_object* x_979; lean_object* x_980; 
x_979 = lean_array_fget(x_5, x_964);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_979);
x_980 = l_Lean_Meta_Grind_internalize(x_979, x_2, x_966, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_909);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; 
x_981 = lean_ctor_get(x_980, 1);
lean_inc(x_981);
lean_dec(x_980);
lean_inc(x_1);
x_982 = l_Lean_Meta_Grind_registerParent(x_1, x_979, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_981);
x_983 = lean_ctor_get(x_982, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_982, 1);
lean_inc(x_984);
lean_dec(x_982);
x_985 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_983, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_984);
lean_dec(x_983);
return x_985;
}
else
{
uint8_t x_986; 
lean_dec(x_979);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_986 = !lean_is_exclusive(x_980);
if (x_986 == 0)
{
return x_980;
}
else
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; 
x_987 = lean_ctor_get(x_980, 0);
x_988 = lean_ctor_get(x_980, 1);
lean_inc(x_988);
lean_inc(x_987);
lean_dec(x_980);
x_989 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_989, 0, x_987);
lean_ctor_set(x_989, 1, x_988);
return x_989;
}
}
}
}
}
block_921:
{
lean_object* x_912; lean_object* x_913; 
lean_dec(x_911);
lean_inc(x_1);
x_912 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_912, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_913 = l_Lean_Meta_Grind_internalize(x_4, x_2, x_912, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_909);
if (lean_obj_tag(x_913) == 0)
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; 
x_914 = lean_ctor_get(x_913, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_913, 1);
lean_inc(x_915);
lean_dec(x_913);
x_916 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_910, x_914, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_915);
lean_dec(x_914);
lean_dec(x_5);
return x_916;
}
else
{
uint8_t x_917; 
lean_dec(x_910);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_917 = !lean_is_exclusive(x_913);
if (x_917 == 0)
{
return x_913;
}
else
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; 
x_918 = lean_ctor_get(x_913, 0);
x_919 = lean_ctor_get(x_913, 1);
lean_inc(x_919);
lean_inc(x_918);
lean_dec(x_913);
x_920 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_920, 0, x_918);
lean_ctor_set(x_920, 1, x_919);
return x_920;
}
}
}
block_956:
{
lean_object* x_923; uint8_t x_924; 
lean_dec(x_922);
x_923 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2;
x_924 = l_Lean_Expr_isConstOf(x_4, x_923);
if (x_924 == 0)
{
lean_object* x_925; 
lean_dec(x_3);
x_925 = lean_box(0);
x_911 = x_925;
goto block_921;
}
else
{
lean_object* x_926; lean_object* x_927; uint8_t x_928; 
x_926 = lean_array_get_size(x_5);
x_927 = lean_unsigned_to_nat(5u);
x_928 = lean_nat_dec_eq(x_926, x_927);
if (x_928 == 0)
{
lean_object* x_929; 
lean_dec(x_926);
lean_dec(x_3);
x_929 = lean_box(0);
x_911 = x_929;
goto block_921;
}
else
{
lean_object* x_930; uint8_t x_931; lean_object* x_932; 
lean_dec(x_910);
lean_dec(x_4);
x_930 = lean_unsigned_to_nat(1u);
x_931 = lean_nat_dec_lt(x_930, x_926);
lean_dec(x_926);
lean_inc(x_1);
x_932 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_932, 0, x_1);
if (x_931 == 0)
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; 
lean_dec(x_5);
x_933 = l_Lean_instInhabitedExpr;
x_934 = l_outOfBounds___rarg(x_933);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_934);
x_935 = l_Lean_Meta_Grind_internalize(x_934, x_2, x_932, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_909);
if (lean_obj_tag(x_935) == 0)
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_936 = lean_ctor_get(x_935, 1);
lean_inc(x_936);
lean_dec(x_935);
lean_inc(x_1);
x_937 = l_Lean_Meta_Grind_registerParent(x_1, x_934, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_936);
x_938 = lean_ctor_get(x_937, 0);
lean_inc(x_938);
x_939 = lean_ctor_get(x_937, 1);
lean_inc(x_939);
lean_dec(x_937);
x_940 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_938, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_939);
lean_dec(x_938);
return x_940;
}
else
{
uint8_t x_941; 
lean_dec(x_934);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_941 = !lean_is_exclusive(x_935);
if (x_941 == 0)
{
return x_935;
}
else
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; 
x_942 = lean_ctor_get(x_935, 0);
x_943 = lean_ctor_get(x_935, 1);
lean_inc(x_943);
lean_inc(x_942);
lean_dec(x_935);
x_944 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_944, 0, x_942);
lean_ctor_set(x_944, 1, x_943);
return x_944;
}
}
}
else
{
lean_object* x_945; lean_object* x_946; 
x_945 = lean_array_fget(x_5, x_930);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_945);
x_946 = l_Lean_Meta_Grind_internalize(x_945, x_2, x_932, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_909);
if (lean_obj_tag(x_946) == 0)
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; 
x_947 = lean_ctor_get(x_946, 1);
lean_inc(x_947);
lean_dec(x_946);
lean_inc(x_1);
x_948 = l_Lean_Meta_Grind_registerParent(x_1, x_945, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_947);
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_948, 1);
lean_inc(x_950);
lean_dec(x_948);
x_951 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_949, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_950);
lean_dec(x_949);
return x_951;
}
else
{
uint8_t x_952; 
lean_dec(x_945);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_952 = !lean_is_exclusive(x_946);
if (x_952 == 0)
{
return x_946;
}
else
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; 
x_953 = lean_ctor_get(x_946, 0);
x_954 = lean_ctor_get(x_946, 1);
lean_inc(x_954);
lean_inc(x_953);
lean_dec(x_946);
x_955 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_955, 0, x_953);
lean_ctor_set(x_955, 1, x_954);
return x_955;
}
}
}
}
}
}
}
else
{
uint8_t x_990; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_990 = !lean_is_exclusive(x_908);
if (x_990 == 0)
{
return x_908;
}
else
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_991 = lean_ctor_get(x_908, 0);
x_992 = lean_ctor_get(x_908, 1);
lean_inc(x_992);
lean_inc(x_991);
lean_dec(x_908);
x_993 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_993, 0, x_991);
lean_ctor_set(x_993, 1, x_992);
return x_993;
}
}
}
else
{
uint8_t x_994; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_994 = !lean_is_exclusive(x_906);
if (x_994 == 0)
{
return x_906;
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; 
x_995 = lean_ctor_get(x_906, 0);
x_996 = lean_ctor_get(x_906, 1);
lean_inc(x_996);
lean_inc(x_995);
lean_dec(x_906);
x_997 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_997, 0, x_995);
lean_ctor_set(x_997, 1, x_996);
return x_997;
}
}
}
else
{
uint8_t x_998; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_998 = !lean_is_exclusive(x_904);
if (x_998 == 0)
{
return x_904;
}
else
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
x_999 = lean_ctor_get(x_904, 0);
x_1000 = lean_ctor_get(x_904, 1);
lean_inc(x_1000);
lean_inc(x_999);
lean_dec(x_904);
x_1001 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1001, 0, x_999);
lean_ctor_set(x_1001, 1, x_1000);
return x_1001;
}
}
}
default: 
{
lean_object* x_1002; 
lean_dec(x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_1002 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_checkAndAddSplitCandidate(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_1002) == 0)
{
lean_object* x_1003; lean_object* x_1004; 
x_1003 = lean_ctor_get(x_1002, 1);
lean_inc(x_1003);
lean_dec(x_1002);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_1004 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1003);
if (lean_obj_tag(x_1004) == 0)
{
lean_object* x_1005; lean_object* x_1006; 
x_1005 = lean_ctor_get(x_1004, 1);
lean_inc(x_1005);
lean_dec(x_1004);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_1006 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(x_4, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1005);
if (lean_obj_tag(x_1006) == 0)
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1020; lean_object* x_1055; uint8_t x_1056; 
x_1007 = lean_ctor_get(x_1006, 1);
lean_inc(x_1007);
lean_dec(x_1006);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_1008 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1___boxed), 13, 3);
lean_closure_set(x_1008, 0, x_1);
lean_closure_set(x_1008, 1, x_2);
lean_closure_set(x_1008, 2, x_3);
x_1055 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4;
x_1056 = l_Lean_Expr_isConstOf(x_4, x_1055);
if (x_1056 == 0)
{
lean_object* x_1057; 
x_1057 = lean_box(0);
x_1020 = x_1057;
goto block_1054;
}
else
{
lean_object* x_1058; lean_object* x_1059; uint8_t x_1060; 
x_1058 = lean_array_get_size(x_5);
x_1059 = lean_unsigned_to_nat(2u);
x_1060 = lean_nat_dec_eq(x_1058, x_1059);
if (x_1060 == 0)
{
lean_object* x_1061; 
lean_dec(x_1058);
x_1061 = lean_box(0);
x_1020 = x_1061;
goto block_1054;
}
else
{
lean_object* x_1062; uint8_t x_1063; lean_object* x_1064; 
lean_dec(x_1008);
lean_dec(x_4);
x_1062 = lean_unsigned_to_nat(0u);
x_1063 = lean_nat_dec_lt(x_1062, x_1058);
lean_dec(x_1058);
lean_inc(x_1);
x_1064 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1064, 0, x_1);
if (x_1063 == 0)
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; 
lean_dec(x_5);
x_1065 = l_Lean_instInhabitedExpr;
x_1066 = l_outOfBounds___rarg(x_1065);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1066);
x_1067 = l_Lean_Meta_Grind_internalize(x_1066, x_2, x_1064, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1007);
if (lean_obj_tag(x_1067) == 0)
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
x_1068 = lean_ctor_get(x_1067, 1);
lean_inc(x_1068);
lean_dec(x_1067);
lean_inc(x_1);
x_1069 = l_Lean_Meta_Grind_registerParent(x_1, x_1066, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1068);
x_1070 = lean_ctor_get(x_1069, 0);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1069, 1);
lean_inc(x_1071);
lean_dec(x_1069);
x_1072 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_1070, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1071);
lean_dec(x_1070);
return x_1072;
}
else
{
uint8_t x_1073; 
lean_dec(x_1066);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1073 = !lean_is_exclusive(x_1067);
if (x_1073 == 0)
{
return x_1067;
}
else
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
x_1074 = lean_ctor_get(x_1067, 0);
x_1075 = lean_ctor_get(x_1067, 1);
lean_inc(x_1075);
lean_inc(x_1074);
lean_dec(x_1067);
x_1076 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1076, 0, x_1074);
lean_ctor_set(x_1076, 1, x_1075);
return x_1076;
}
}
}
else
{
lean_object* x_1077; lean_object* x_1078; 
x_1077 = lean_array_fget(x_5, x_1062);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1077);
x_1078 = l_Lean_Meta_Grind_internalize(x_1077, x_2, x_1064, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1007);
if (lean_obj_tag(x_1078) == 0)
{
lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
x_1079 = lean_ctor_get(x_1078, 1);
lean_inc(x_1079);
lean_dec(x_1078);
lean_inc(x_1);
x_1080 = l_Lean_Meta_Grind_registerParent(x_1, x_1077, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1079);
x_1081 = lean_ctor_get(x_1080, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1080, 1);
lean_inc(x_1082);
lean_dec(x_1080);
x_1083 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_1081, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1082);
lean_dec(x_1081);
return x_1083;
}
else
{
uint8_t x_1084; 
lean_dec(x_1077);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1084 = !lean_is_exclusive(x_1078);
if (x_1084 == 0)
{
return x_1078;
}
else
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1085 = lean_ctor_get(x_1078, 0);
x_1086 = lean_ctor_get(x_1078, 1);
lean_inc(x_1086);
lean_inc(x_1085);
lean_dec(x_1078);
x_1087 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1087, 0, x_1085);
lean_ctor_set(x_1087, 1, x_1086);
return x_1087;
}
}
}
}
}
block_1019:
{
lean_object* x_1010; lean_object* x_1011; 
lean_dec(x_1009);
lean_inc(x_1);
x_1010 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1010, 0, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_1011 = l_Lean_Meta_Grind_internalize(x_4, x_2, x_1010, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1007);
if (lean_obj_tag(x_1011) == 0)
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; 
x_1012 = lean_ctor_get(x_1011, 0);
lean_inc(x_1012);
x_1013 = lean_ctor_get(x_1011, 1);
lean_inc(x_1013);
lean_dec(x_1011);
x_1014 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2(x_1, x_4, x_5, x_2, x_1008, x_1012, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1013);
lean_dec(x_1012);
lean_dec(x_5);
return x_1014;
}
else
{
uint8_t x_1015; 
lean_dec(x_1008);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1015 = !lean_is_exclusive(x_1011);
if (x_1015 == 0)
{
return x_1011;
}
else
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
x_1016 = lean_ctor_get(x_1011, 0);
x_1017 = lean_ctor_get(x_1011, 1);
lean_inc(x_1017);
lean_inc(x_1016);
lean_dec(x_1011);
x_1018 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1018, 0, x_1016);
lean_ctor_set(x_1018, 1, x_1017);
return x_1018;
}
}
}
block_1054:
{
lean_object* x_1021; uint8_t x_1022; 
lean_dec(x_1020);
x_1021 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2;
x_1022 = l_Lean_Expr_isConstOf(x_4, x_1021);
if (x_1022 == 0)
{
lean_object* x_1023; 
lean_dec(x_3);
x_1023 = lean_box(0);
x_1009 = x_1023;
goto block_1019;
}
else
{
lean_object* x_1024; lean_object* x_1025; uint8_t x_1026; 
x_1024 = lean_array_get_size(x_5);
x_1025 = lean_unsigned_to_nat(5u);
x_1026 = lean_nat_dec_eq(x_1024, x_1025);
if (x_1026 == 0)
{
lean_object* x_1027; 
lean_dec(x_1024);
lean_dec(x_3);
x_1027 = lean_box(0);
x_1009 = x_1027;
goto block_1019;
}
else
{
lean_object* x_1028; uint8_t x_1029; lean_object* x_1030; 
lean_dec(x_1008);
lean_dec(x_4);
x_1028 = lean_unsigned_to_nat(1u);
x_1029 = lean_nat_dec_lt(x_1028, x_1024);
lean_dec(x_1024);
lean_inc(x_1);
x_1030 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1030, 0, x_1);
if (x_1029 == 0)
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
lean_dec(x_5);
x_1031 = l_Lean_instInhabitedExpr;
x_1032 = l_outOfBounds___rarg(x_1031);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1032);
x_1033 = l_Lean_Meta_Grind_internalize(x_1032, x_2, x_1030, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1007);
if (lean_obj_tag(x_1033) == 0)
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1034 = lean_ctor_get(x_1033, 1);
lean_inc(x_1034);
lean_dec(x_1033);
lean_inc(x_1);
x_1035 = l_Lean_Meta_Grind_registerParent(x_1, x_1032, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1034);
x_1036 = lean_ctor_get(x_1035, 0);
lean_inc(x_1036);
x_1037 = lean_ctor_get(x_1035, 1);
lean_inc(x_1037);
lean_dec(x_1035);
x_1038 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_1036, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1037);
lean_dec(x_1036);
return x_1038;
}
else
{
uint8_t x_1039; 
lean_dec(x_1032);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1039 = !lean_is_exclusive(x_1033);
if (x_1039 == 0)
{
return x_1033;
}
else
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1040 = lean_ctor_get(x_1033, 0);
x_1041 = lean_ctor_get(x_1033, 1);
lean_inc(x_1041);
lean_inc(x_1040);
lean_dec(x_1033);
x_1042 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1042, 0, x_1040);
lean_ctor_set(x_1042, 1, x_1041);
return x_1042;
}
}
}
else
{
lean_object* x_1043; lean_object* x_1044; 
x_1043 = lean_array_fget(x_5, x_1028);
lean_dec(x_5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1043);
x_1044 = l_Lean_Meta_Grind_internalize(x_1043, x_2, x_1030, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1007);
if (lean_obj_tag(x_1044) == 0)
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; 
x_1045 = lean_ctor_get(x_1044, 1);
lean_inc(x_1045);
lean_dec(x_1044);
lean_inc(x_1);
x_1046 = l_Lean_Meta_Grind_registerParent(x_1, x_1043, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1045);
x_1047 = lean_ctor_get(x_1046, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1046, 1);
lean_inc(x_1048);
lean_dec(x_1046);
x_1049 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_1047, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_1048);
lean_dec(x_1047);
return x_1049;
}
else
{
uint8_t x_1050; 
lean_dec(x_1043);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1050 = !lean_is_exclusive(x_1044);
if (x_1050 == 0)
{
return x_1044;
}
else
{
lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
x_1051 = lean_ctor_get(x_1044, 0);
x_1052 = lean_ctor_get(x_1044, 1);
lean_inc(x_1052);
lean_inc(x_1051);
lean_dec(x_1044);
x_1053 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1053, 0, x_1051);
lean_ctor_set(x_1053, 1, x_1052);
return x_1053;
}
}
}
}
}
}
}
else
{
uint8_t x_1088; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1088 = !lean_is_exclusive(x_1006);
if (x_1088 == 0)
{
return x_1006;
}
else
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
x_1089 = lean_ctor_get(x_1006, 0);
x_1090 = lean_ctor_get(x_1006, 1);
lean_inc(x_1090);
lean_inc(x_1089);
lean_dec(x_1006);
x_1091 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1091, 0, x_1089);
lean_ctor_set(x_1091, 1, x_1090);
return x_1091;
}
}
}
else
{
uint8_t x_1092; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1092 = !lean_is_exclusive(x_1004);
if (x_1092 == 0)
{
return x_1004;
}
else
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; 
x_1093 = lean_ctor_get(x_1004, 0);
x_1094 = lean_ctor_get(x_1004, 1);
lean_inc(x_1094);
lean_inc(x_1093);
lean_dec(x_1004);
x_1095 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1095, 0, x_1093);
lean_ctor_set(x_1095, 1, x_1094);
return x_1095;
}
}
}
else
{
uint8_t x_1096; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1096 = !lean_is_exclusive(x_1002);
if (x_1096 == 0)
{
return x_1002;
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
x_1097 = lean_ctor_get(x_1002, 0);
x_1098 = lean_ctor_get(x_1002, 1);
lean_inc(x_1098);
lean_inc(x_1097);
lean_dec(x_1002);
x_1099 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1099, 0, x_1097);
lean_ctor_set(x_1099, 1, x_1098);
return x_1099;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_internalize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_propagateUp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Internalize", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.internalize", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_internalize___lambda__2___closed__1;
x_2 = l_Lean_Meta_Grind_internalize___lambda__2___closed__2;
x_3 = lean_unsigned_to_nat(178u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Lean_Meta_Grind_internalize___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected kernel projection term during internalization", 56, 56);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_internalize___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n`grind` uses a pre-processing step that folds them as projection applications, the pre-processor should have failed to fold this term", 134, 134);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_internalize___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("MatchCond", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2;
x_3 = l_Lean_Meta_Grind_internalize___lambda__2___closed__9;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_internalize___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Meta_Grind_internalize___lambda__2___closed__4;
x_15 = l_panic___at___private_Lean_Meta_Tactic_Grind_Arith_Offset_0__Lean_Meta_Grind_Arith_Offset_setUnsat___spec__1(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
lean_dec(x_3);
lean_inc(x_1);
x_16 = l_Lean_indentExpr(x_1);
x_17 = l_Lean_Meta_Grind_internalize___lambda__2___closed__6;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Meta_Grind_internalize___lambda__2___closed__8;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_Grind_reportIssue(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 0;
x_24 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_23, x_23, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
case 3:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
return x_26;
}
case 4:
{
lean_object* x_27; 
lean_dec(x_3);
x_27 = l_Lean_Meta_Grind_mkENode(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_27;
}
case 5:
{
lean_object* x_28; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_28 = l_Lean_Meta_isLitValue(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Meta_Grind_internalize___lambda__2___closed__10;
x_33 = lean_unsigned_to_nat(1u);
x_34 = l_Lean_Expr_isAppOfArity(x_1, x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_unsigned_to_nat(0u);
x_36 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_35);
x_37 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1;
lean_inc(x_36);
x_38 = lean_mk_array(x_36, x_37);
x_39 = lean_nat_sub(x_36, x_33);
lean_dec(x_36);
lean_inc(x_1);
x_40 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2(x_1, x_2, x_3, x_1, x_38, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_3);
x_41 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_dec(x_28);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_43 = l_Lean_Meta_Grind_mkENode(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Meta_Grind_Arith_Offset_internalize(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_28);
if (x_50 == 0)
{
return x_28;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_28, 0);
x_52 = lean_ctor_get(x_28, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_28);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
case 7:
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_85; 
lean_dec(x_3);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 2);
lean_inc(x_55);
x_56 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_57 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_56, x_56, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_54);
x_85 = l_Lean_Meta_isProp(x_54, x_9, x_10, x_11, x_12, x_58);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_unbox(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_unbox(x_86);
lean_dec(x_86);
x_60 = x_89;
x_61 = x_88;
goto block_84;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_86);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_91 = l_Lean_Meta_isProp(x_1, x_9, x_10, x_11, x_12, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_unbox(x_92);
lean_dec(x_92);
x_60 = x_94;
x_61 = x_93;
goto block_84;
}
else
{
uint8_t x_95; 
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_91);
if (x_95 == 0)
{
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_91, 0);
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_91);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_85);
if (x_99 == 0)
{
return x_85;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_85, 0);
x_101 = lean_ctor_get(x_85, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_85);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
block_84:
{
if (x_60 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
lean_inc(x_1);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_64);
lean_inc(x_2);
lean_inc(x_54);
x_65 = l_Lean_Meta_Grind_internalize(x_54, x_2, x_64, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_61);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
lean_inc(x_1);
x_67 = l_Lean_Meta_Grind_registerParent(x_1, x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_66);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Expr_hasLooseBVars(x_55);
if (x_69 == 0)
{
lean_object* x_70; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_55);
x_70 = l_Lean_Meta_Grind_internalize(x_55, x_2, x_64, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
lean_inc(x_1);
x_72 = l_Lean_Meta_Grind_registerParent(x_1, x_55, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_71);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_Meta_Grind_propagateUp(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_73);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_55);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_70);
if (x_75 == 0)
{
return x_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_70, 0);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_70);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_64);
lean_dec(x_55);
lean_dec(x_2);
x_79 = l_Lean_Meta_Grind_propagateUp(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_68);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_64);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_65);
if (x_80 == 0)
{
return x_65;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_65, 0);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_65);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
case 9:
{
lean_object* x_103; 
lean_dec(x_3);
x_103 = l_Lean_Meta_Grind_mkENode(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_103;
}
case 10:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; 
lean_dec(x_3);
lean_inc(x_1);
x_104 = l_Lean_indentExpr(x_1);
x_105 = l_Lean_Meta_Grind_internalize___lambda__2___closed__6;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_Lean_Meta_Grind_internalize___lambda__2___closed__8;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_Meta_Grind_reportIssue(x_108, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = 0;
x_112 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_111, x_111, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_110);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_112;
}
case 11:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; 
lean_dec(x_3);
lean_inc(x_1);
x_113 = l_Lean_indentExpr(x_1);
x_114 = l_Lean_Meta_Grind_internalize___lambda__2___closed__6;
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_Lean_Meta_Grind_internalize___lambda__2___closed__8;
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_Meta_Grind_reportIssue(x_117, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = 0;
x_121 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_120, x_120, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_119);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_121;
}
default: 
{
uint8_t x_122; lean_object* x_123; 
lean_dec(x_3);
x_122 = 0;
x_123 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_122, x_122, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_123;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_internalize___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internalize", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_internalize___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1;
x_2 = l_Lean_Meta_Grind_internalize___lambda__3___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_internalize___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l_Lean_Meta_Grind_internalize___lambda__3___closed__2;
x_15 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = l_Lean_Meta_Grind_internalize___lambda__2(x_1, x_2, x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 1);
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_24 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_1);
x_26 = l_Lean_MessageData_ofExpr(x_1);
x_27 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_26);
lean_ctor_set(x_15, 0, x_27);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_14, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_Grind_internalize___lambda__2(x_1, x_2, x_3, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
lean_dec(x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_dec(x_15);
x_38 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_1);
x_40 = l_Lean_MessageData_ofExpr(x_1);
x_41 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_14, x_43, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_Grind_internalize___lambda__2(x_1, x_2, x_3, x_45, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_46);
lean_dec(x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_50 = x_38;
} else {
 lean_dec_ref(x_38);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_internalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Meta_Grind_alreadyInternalized(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Grind_internalize___lambda__3(x_1, x_2, x_3, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_usize_shift_right(x_2, x_5);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__3(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_HeadIndex_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__1(x_1, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
x_13 = l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__1(x_1, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_3);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_dec(x_11);
x_2 = x_12;
goto _start;
}
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_take(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_13, 13);
x_17 = l_Lean_Meta_Grind_EMatchTheorems_insert(x_16, x_1);
lean_ctor_set(x_13, 13, x_17);
x_18 = lean_st_ref_set(x_3, x_13, x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
x_27 = lean_ctor_get(x_13, 2);
x_28 = lean_ctor_get(x_13, 3);
x_29 = lean_ctor_get(x_13, 4);
x_30 = lean_ctor_get(x_13, 5);
x_31 = lean_ctor_get(x_13, 6);
x_32 = lean_ctor_get_uint8(x_13, sizeof(void*)*26);
x_33 = lean_ctor_get(x_13, 7);
x_34 = lean_ctor_get(x_13, 8);
x_35 = lean_ctor_get(x_13, 9);
x_36 = lean_ctor_get(x_13, 10);
x_37 = lean_ctor_get(x_13, 11);
x_38 = lean_ctor_get(x_13, 12);
x_39 = lean_ctor_get(x_13, 13);
x_40 = lean_ctor_get(x_13, 14);
x_41 = lean_ctor_get(x_13, 15);
x_42 = lean_ctor_get(x_13, 16);
x_43 = lean_ctor_get(x_13, 17);
x_44 = lean_ctor_get(x_13, 18);
x_45 = lean_ctor_get(x_13, 19);
x_46 = lean_ctor_get(x_13, 20);
x_47 = lean_ctor_get(x_13, 21);
x_48 = lean_ctor_get(x_13, 22);
x_49 = lean_ctor_get(x_13, 23);
x_50 = lean_ctor_get(x_13, 24);
x_51 = lean_ctor_get(x_13, 25);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_52 = l_Lean_Meta_Grind_EMatchTheorems_insert(x_39, x_1);
x_53 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_53, 0, x_25);
lean_ctor_set(x_53, 1, x_26);
lean_ctor_set(x_53, 2, x_27);
lean_ctor_set(x_53, 3, x_28);
lean_ctor_set(x_53, 4, x_29);
lean_ctor_set(x_53, 5, x_30);
lean_ctor_set(x_53, 6, x_31);
lean_ctor_set(x_53, 7, x_33);
lean_ctor_set(x_53, 8, x_34);
lean_ctor_set(x_53, 9, x_35);
lean_ctor_set(x_53, 10, x_36);
lean_ctor_set(x_53, 11, x_37);
lean_ctor_set(x_53, 12, x_38);
lean_ctor_set(x_53, 13, x_52);
lean_ctor_set(x_53, 14, x_40);
lean_ctor_set(x_53, 15, x_41);
lean_ctor_set(x_53, 16, x_42);
lean_ctor_set(x_53, 17, x_43);
lean_ctor_set(x_53, 18, x_44);
lean_ctor_set(x_53, 19, x_45);
lean_ctor_set(x_53, 20, x_46);
lean_ctor_set(x_53, 21, x_47);
lean_ctor_set(x_53, 22, x_48);
lean_ctor_set(x_53, 23, x_49);
lean_ctor_set(x_53, 24, x_50);
lean_ctor_set(x_53, 25, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*26, x_32);
x_54 = lean_st_ref_set(x_3, x_53, x_14);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ematch", 6, 6);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1;
x_2 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reinsert `", 10, 10);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_7);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
x_26 = lean_st_ref_get(x_9, x_17);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 13);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
x_33 = lean_ctor_get(x_19, 2);
x_34 = lean_ctor_get(x_19, 3);
x_35 = lean_ctor_get(x_19, 4);
x_36 = lean_ctor_get(x_19, 5);
x_37 = l_Lean_Meta_Grind_EMatchTheorems_isErased(x_29, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
lean_inc(x_3);
x_39 = l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__4(x_3, x_35, x_38);
lean_inc(x_36);
lean_inc(x_39);
lean_ctor_set(x_19, 4, x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_40 = l_Lean_Meta_Grind_activateTheorem(x_19, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
x_21 = x_42;
x_22 = x_41;
goto block_25;
}
else
{
uint8_t x_43; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_39, 1);
lean_dec(x_48);
x_49 = lean_ctor_get(x_39, 0);
lean_dec(x_49);
x_50 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2;
x_51 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_50, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_39);
lean_dec(x_36);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_box(0);
x_56 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_19, x_55, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_54);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_21 = x_57;
x_22 = x_58;
goto block_25;
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_51);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_51, 1);
x_61 = lean_ctor_get(x_51, 0);
lean_dec(x_61);
x_62 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_Meta_Grind_Origin_key(x_36);
lean_dec(x_36);
x_65 = l_Lean_MessageData_ofName(x_64);
x_66 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4;
lean_ctor_set_tag(x_51, 7);
lean_ctor_set(x_51, 1, x_65);
lean_ctor_set(x_51, 0, x_66);
x_67 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__6;
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_67);
lean_ctor_set(x_39, 0, x_51);
x_68 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_50, x_39, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_63);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_19, x_69, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_70);
lean_dec(x_69);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_21 = x_72;
x_22 = x_73;
goto block_25;
}
else
{
uint8_t x_74; 
lean_free_object(x_51);
lean_free_object(x_39);
lean_dec(x_19);
lean_dec(x_36);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_62);
if (x_74 == 0)
{
return x_62;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_62, 0);
x_76 = lean_ctor_get(x_62, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_62);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_51, 1);
lean_inc(x_78);
lean_dec(x_51);
x_79 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l_Lean_Meta_Grind_Origin_key(x_36);
lean_dec(x_36);
x_82 = l_Lean_MessageData_ofName(x_81);
x_83 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__6;
lean_ctor_set_tag(x_39, 7);
lean_ctor_set(x_39, 1, x_85);
lean_ctor_set(x_39, 0, x_84);
x_86 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_50, x_39, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_80);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_19, x_87, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_88);
lean_dec(x_87);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_21 = x_90;
x_22 = x_91;
goto block_25;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_free_object(x_39);
lean_dec(x_19);
lean_dec(x_36);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_92 = lean_ctor_get(x_79, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_79, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_94 = x_79;
} else {
 lean_dec_ref(x_79);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec(x_39);
x_96 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2;
x_97 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_96, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_36);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_box(0);
x_102 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_19, x_101, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_100);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_21 = x_103;
x_22 = x_104;
goto block_25;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_97, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_106 = x_97;
} else {
 lean_dec_ref(x_97);
 x_106 = lean_box(0);
}
x_107 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_105);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = l_Lean_Meta_Grind_Origin_key(x_36);
lean_dec(x_36);
x_110 = l_Lean_MessageData_ofName(x_109);
x_111 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4;
if (lean_is_scalar(x_106)) {
 x_112 = lean_alloc_ctor(7, 2, 0);
} else {
 x_112 = x_106;
 lean_ctor_set_tag(x_112, 7);
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__6;
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_96, x_114, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_108);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_19, x_116, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_117);
lean_dec(x_116);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_21 = x_119;
x_22 = x_120;
goto block_25;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_106);
lean_dec(x_19);
lean_dec(x_36);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_121 = lean_ctor_get(x_107, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_107, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_123 = x_107;
} else {
 lean_dec_ref(x_107);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
}
else
{
lean_object* x_125; 
lean_free_object(x_19);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_125 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
x_21 = x_125;
x_22 = x_28;
goto block_25;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_126 = lean_ctor_get(x_19, 0);
x_127 = lean_ctor_get(x_19, 1);
x_128 = lean_ctor_get(x_19, 2);
x_129 = lean_ctor_get(x_19, 3);
x_130 = lean_ctor_get(x_19, 4);
x_131 = lean_ctor_get(x_19, 5);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_19);
x_132 = l_Lean_Meta_Grind_EMatchTheorems_isErased(x_29, x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_box(0);
lean_inc(x_3);
x_134 = l_List_filterTR_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__4(x_3, x_130, x_133);
lean_inc(x_131);
lean_inc(x_134);
x_135 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_135, 0, x_126);
lean_ctor_set(x_135, 1, x_127);
lean_ctor_set(x_135, 2, x_128);
lean_ctor_set(x_135, 3, x_129);
lean_ctor_set(x_135, 4, x_134);
lean_ctor_set(x_135, 5, x_131);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_136; 
lean_dec(x_131);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_136 = l_Lean_Meta_Grind_activateTheorem(x_135, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
x_21 = x_138;
x_22 = x_137;
goto block_25;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_141 = x_136;
} else {
 lean_dec_ref(x_136);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_143 = x_134;
} else {
 lean_dec_ref(x_134);
 x_143 = lean_box(0);
}
x_144 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2;
x_145 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_144, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_143);
lean_dec(x_131);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_box(0);
x_150 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_135, x_149, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_148);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_21 = x_151;
x_22 = x_152;
goto block_25;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_145, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_154 = x_145;
} else {
 lean_dec_ref(x_145);
 x_154 = lean_box(0);
}
x_155 = l_Lean_Meta_Grind_updateLastTag(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_153);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = l_Lean_Meta_Grind_Origin_key(x_131);
lean_dec(x_131);
x_158 = l_Lean_MessageData_ofName(x_157);
x_159 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4;
if (lean_is_scalar(x_154)) {
 x_160 = lean_alloc_ctor(7, 2, 0);
} else {
 x_160 = x_154;
 lean_ctor_set_tag(x_160, 7);
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__6;
if (lean_is_scalar(x_143)) {
 x_162 = lean_alloc_ctor(7, 2, 0);
} else {
 x_162 = x_143;
 lean_ctor_set_tag(x_162, 7);
}
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_144, x_162, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_156);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_135, x_164, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_165);
lean_dec(x_164);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_21 = x_167;
x_22 = x_168;
goto block_25;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_154);
lean_dec(x_143);
lean_dec(x_135);
lean_dec(x_131);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_169 = lean_ctor_get(x_155, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_155, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_171 = x_155;
} else {
 lean_dec_ref(x_155);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
}
else
{
lean_object* x_173; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
x_173 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1;
x_21 = x_173;
x_22 = x_28;
goto block_25;
}
}
block_25:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_6 = x_20;
x_7 = x_23;
x_8 = lean_box(0);
x_17 = x_22;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 13);
lean_inc(x_14);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
x_21 = lean_ctor_get(x_14, 2);
lean_inc(x_19);
x_22 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_EMatchTheorems_insert___spec__9(x_19, x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_free_object(x_14);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(0);
lean_ctor_set(x_12, 0, x_23);
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_free_object(x_12);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_PersistentHashMap_erase___at_Lean_Meta_Grind_EMatchTheorems_retrieve_x3f___spec__1(x_19, x_1);
lean_ctor_set(x_14, 0, x_25);
x_26 = lean_st_ref_take(x_3, x_16);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_27, 13);
lean_dec(x_30);
lean_ctor_set(x_27, 13, x_14);
x_31 = lean_st_ref_set(x_3, x_27, x_28);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_get(x_3, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 5);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_box(0);
x_38 = lean_box(0);
lean_inc(x_24);
x_39 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(x_2, x_24, x_36, x_37, x_24, x_24, x_38, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_24);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_48 = lean_ctor_get(x_27, 0);
x_49 = lean_ctor_get(x_27, 1);
x_50 = lean_ctor_get(x_27, 2);
x_51 = lean_ctor_get(x_27, 3);
x_52 = lean_ctor_get(x_27, 4);
x_53 = lean_ctor_get(x_27, 5);
x_54 = lean_ctor_get(x_27, 6);
x_55 = lean_ctor_get_uint8(x_27, sizeof(void*)*26);
x_56 = lean_ctor_get(x_27, 7);
x_57 = lean_ctor_get(x_27, 8);
x_58 = lean_ctor_get(x_27, 9);
x_59 = lean_ctor_get(x_27, 10);
x_60 = lean_ctor_get(x_27, 11);
x_61 = lean_ctor_get(x_27, 12);
x_62 = lean_ctor_get(x_27, 14);
x_63 = lean_ctor_get(x_27, 15);
x_64 = lean_ctor_get(x_27, 16);
x_65 = lean_ctor_get(x_27, 17);
x_66 = lean_ctor_get(x_27, 18);
x_67 = lean_ctor_get(x_27, 19);
x_68 = lean_ctor_get(x_27, 20);
x_69 = lean_ctor_get(x_27, 21);
x_70 = lean_ctor_get(x_27, 22);
x_71 = lean_ctor_get(x_27, 23);
x_72 = lean_ctor_get(x_27, 24);
x_73 = lean_ctor_get(x_27, 25);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_27);
x_74 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_74, 0, x_48);
lean_ctor_set(x_74, 1, x_49);
lean_ctor_set(x_74, 2, x_50);
lean_ctor_set(x_74, 3, x_51);
lean_ctor_set(x_74, 4, x_52);
lean_ctor_set(x_74, 5, x_53);
lean_ctor_set(x_74, 6, x_54);
lean_ctor_set(x_74, 7, x_56);
lean_ctor_set(x_74, 8, x_57);
lean_ctor_set(x_74, 9, x_58);
lean_ctor_set(x_74, 10, x_59);
lean_ctor_set(x_74, 11, x_60);
lean_ctor_set(x_74, 12, x_61);
lean_ctor_set(x_74, 13, x_14);
lean_ctor_set(x_74, 14, x_62);
lean_ctor_set(x_74, 15, x_63);
lean_ctor_set(x_74, 16, x_64);
lean_ctor_set(x_74, 17, x_65);
lean_ctor_set(x_74, 18, x_66);
lean_ctor_set(x_74, 19, x_67);
lean_ctor_set(x_74, 20, x_68);
lean_ctor_set(x_74, 21, x_69);
lean_ctor_set(x_74, 22, x_70);
lean_ctor_set(x_74, 23, x_71);
lean_ctor_set(x_74, 24, x_72);
lean_ctor_set(x_74, 25, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*26, x_55);
x_75 = lean_st_ref_set(x_3, x_74, x_28);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_st_ref_get(x_3, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 5);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_box(0);
x_82 = lean_box(0);
lean_inc(x_24);
x_83 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(x_2, x_24, x_80, x_81, x_24, x_24, x_82, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_79);
lean_dec(x_24);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_89 = x_83;
} else {
 lean_dec_ref(x_83);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_14, 0);
x_92 = lean_ctor_get(x_14, 1);
x_93 = lean_ctor_get(x_14, 2);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_14);
lean_inc(x_91);
x_94 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_EMatchTheorems_insert___spec__9(x_91, x_1);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = lean_box(0);
lean_ctor_set(x_12, 0, x_95);
return x_12;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_free_object(x_12);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_PersistentHashMap_erase___at_Lean_Meta_Grind_EMatchTheorems_retrieve_x3f___spec__1(x_91, x_1);
x_98 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_92);
lean_ctor_set(x_98, 2, x_93);
x_99 = lean_st_ref_take(x_3, x_16);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_100, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_100, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_100, 4);
lean_inc(x_106);
x_107 = lean_ctor_get(x_100, 5);
lean_inc(x_107);
x_108 = lean_ctor_get(x_100, 6);
lean_inc(x_108);
x_109 = lean_ctor_get_uint8(x_100, sizeof(void*)*26);
x_110 = lean_ctor_get(x_100, 7);
lean_inc(x_110);
x_111 = lean_ctor_get(x_100, 8);
lean_inc(x_111);
x_112 = lean_ctor_get(x_100, 9);
lean_inc(x_112);
x_113 = lean_ctor_get(x_100, 10);
lean_inc(x_113);
x_114 = lean_ctor_get(x_100, 11);
lean_inc(x_114);
x_115 = lean_ctor_get(x_100, 12);
lean_inc(x_115);
x_116 = lean_ctor_get(x_100, 14);
lean_inc(x_116);
x_117 = lean_ctor_get(x_100, 15);
lean_inc(x_117);
x_118 = lean_ctor_get(x_100, 16);
lean_inc(x_118);
x_119 = lean_ctor_get(x_100, 17);
lean_inc(x_119);
x_120 = lean_ctor_get(x_100, 18);
lean_inc(x_120);
x_121 = lean_ctor_get(x_100, 19);
lean_inc(x_121);
x_122 = lean_ctor_get(x_100, 20);
lean_inc(x_122);
x_123 = lean_ctor_get(x_100, 21);
lean_inc(x_123);
x_124 = lean_ctor_get(x_100, 22);
lean_inc(x_124);
x_125 = lean_ctor_get(x_100, 23);
lean_inc(x_125);
x_126 = lean_ctor_get(x_100, 24);
lean_inc(x_126);
x_127 = lean_ctor_get(x_100, 25);
lean_inc(x_127);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 lean_ctor_release(x_100, 2);
 lean_ctor_release(x_100, 3);
 lean_ctor_release(x_100, 4);
 lean_ctor_release(x_100, 5);
 lean_ctor_release(x_100, 6);
 lean_ctor_release(x_100, 7);
 lean_ctor_release(x_100, 8);
 lean_ctor_release(x_100, 9);
 lean_ctor_release(x_100, 10);
 lean_ctor_release(x_100, 11);
 lean_ctor_release(x_100, 12);
 lean_ctor_release(x_100, 13);
 lean_ctor_release(x_100, 14);
 lean_ctor_release(x_100, 15);
 lean_ctor_release(x_100, 16);
 lean_ctor_release(x_100, 17);
 lean_ctor_release(x_100, 18);
 lean_ctor_release(x_100, 19);
 lean_ctor_release(x_100, 20);
 lean_ctor_release(x_100, 21);
 lean_ctor_release(x_100, 22);
 lean_ctor_release(x_100, 23);
 lean_ctor_release(x_100, 24);
 lean_ctor_release(x_100, 25);
 x_128 = x_100;
} else {
 lean_dec_ref(x_100);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 26, 1);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_102);
lean_ctor_set(x_129, 1, x_103);
lean_ctor_set(x_129, 2, x_104);
lean_ctor_set(x_129, 3, x_105);
lean_ctor_set(x_129, 4, x_106);
lean_ctor_set(x_129, 5, x_107);
lean_ctor_set(x_129, 6, x_108);
lean_ctor_set(x_129, 7, x_110);
lean_ctor_set(x_129, 8, x_111);
lean_ctor_set(x_129, 9, x_112);
lean_ctor_set(x_129, 10, x_113);
lean_ctor_set(x_129, 11, x_114);
lean_ctor_set(x_129, 12, x_115);
lean_ctor_set(x_129, 13, x_98);
lean_ctor_set(x_129, 14, x_116);
lean_ctor_set(x_129, 15, x_117);
lean_ctor_set(x_129, 16, x_118);
lean_ctor_set(x_129, 17, x_119);
lean_ctor_set(x_129, 18, x_120);
lean_ctor_set(x_129, 19, x_121);
lean_ctor_set(x_129, 20, x_122);
lean_ctor_set(x_129, 21, x_123);
lean_ctor_set(x_129, 22, x_124);
lean_ctor_set(x_129, 23, x_125);
lean_ctor_set(x_129, 24, x_126);
lean_ctor_set(x_129, 25, x_127);
lean_ctor_set_uint8(x_129, sizeof(void*)*26, x_109);
x_130 = lean_st_ref_set(x_3, x_129, x_101);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_st_ref_get(x_3, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_133, 5);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_box(0);
x_137 = lean_box(0);
lean_inc(x_96);
x_138 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(x_2, x_96, x_135, x_136, x_96, x_96, x_137, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_134);
lean_dec(x_96);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_137);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_138, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_144 = x_138;
} else {
 lean_dec_ref(x_138);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_12, 1);
lean_inc(x_146);
lean_dec(x_12);
x_147 = lean_ctor_get(x_14, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_14, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_14, 2);
lean_inc(x_149);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_150 = x_14;
} else {
 lean_dec_ref(x_14);
 x_150 = lean_box(0);
}
lean_inc(x_147);
x_151 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Grind_EMatchTheorems_insert___spec__9(x_147, x_1);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_146);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
lean_dec(x_151);
x_155 = l_Lean_PersistentHashMap_erase___at_Lean_Meta_Grind_EMatchTheorems_retrieve_x3f___spec__1(x_147, x_1);
if (lean_is_scalar(x_150)) {
 x_156 = lean_alloc_ctor(0, 3, 0);
} else {
 x_156 = x_150;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_148);
lean_ctor_set(x_156, 2, x_149);
x_157 = lean_st_ref_take(x_3, x_146);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 2);
lean_inc(x_162);
x_163 = lean_ctor_get(x_158, 3);
lean_inc(x_163);
x_164 = lean_ctor_get(x_158, 4);
lean_inc(x_164);
x_165 = lean_ctor_get(x_158, 5);
lean_inc(x_165);
x_166 = lean_ctor_get(x_158, 6);
lean_inc(x_166);
x_167 = lean_ctor_get_uint8(x_158, sizeof(void*)*26);
x_168 = lean_ctor_get(x_158, 7);
lean_inc(x_168);
x_169 = lean_ctor_get(x_158, 8);
lean_inc(x_169);
x_170 = lean_ctor_get(x_158, 9);
lean_inc(x_170);
x_171 = lean_ctor_get(x_158, 10);
lean_inc(x_171);
x_172 = lean_ctor_get(x_158, 11);
lean_inc(x_172);
x_173 = lean_ctor_get(x_158, 12);
lean_inc(x_173);
x_174 = lean_ctor_get(x_158, 14);
lean_inc(x_174);
x_175 = lean_ctor_get(x_158, 15);
lean_inc(x_175);
x_176 = lean_ctor_get(x_158, 16);
lean_inc(x_176);
x_177 = lean_ctor_get(x_158, 17);
lean_inc(x_177);
x_178 = lean_ctor_get(x_158, 18);
lean_inc(x_178);
x_179 = lean_ctor_get(x_158, 19);
lean_inc(x_179);
x_180 = lean_ctor_get(x_158, 20);
lean_inc(x_180);
x_181 = lean_ctor_get(x_158, 21);
lean_inc(x_181);
x_182 = lean_ctor_get(x_158, 22);
lean_inc(x_182);
x_183 = lean_ctor_get(x_158, 23);
lean_inc(x_183);
x_184 = lean_ctor_get(x_158, 24);
lean_inc(x_184);
x_185 = lean_ctor_get(x_158, 25);
lean_inc(x_185);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 lean_ctor_release(x_158, 5);
 lean_ctor_release(x_158, 6);
 lean_ctor_release(x_158, 7);
 lean_ctor_release(x_158, 8);
 lean_ctor_release(x_158, 9);
 lean_ctor_release(x_158, 10);
 lean_ctor_release(x_158, 11);
 lean_ctor_release(x_158, 12);
 lean_ctor_release(x_158, 13);
 lean_ctor_release(x_158, 14);
 lean_ctor_release(x_158, 15);
 lean_ctor_release(x_158, 16);
 lean_ctor_release(x_158, 17);
 lean_ctor_release(x_158, 18);
 lean_ctor_release(x_158, 19);
 lean_ctor_release(x_158, 20);
 lean_ctor_release(x_158, 21);
 lean_ctor_release(x_158, 22);
 lean_ctor_release(x_158, 23);
 lean_ctor_release(x_158, 24);
 lean_ctor_release(x_158, 25);
 x_186 = x_158;
} else {
 lean_dec_ref(x_158);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(0, 26, 1);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_160);
lean_ctor_set(x_187, 1, x_161);
lean_ctor_set(x_187, 2, x_162);
lean_ctor_set(x_187, 3, x_163);
lean_ctor_set(x_187, 4, x_164);
lean_ctor_set(x_187, 5, x_165);
lean_ctor_set(x_187, 6, x_166);
lean_ctor_set(x_187, 7, x_168);
lean_ctor_set(x_187, 8, x_169);
lean_ctor_set(x_187, 9, x_170);
lean_ctor_set(x_187, 10, x_171);
lean_ctor_set(x_187, 11, x_172);
lean_ctor_set(x_187, 12, x_173);
lean_ctor_set(x_187, 13, x_156);
lean_ctor_set(x_187, 14, x_174);
lean_ctor_set(x_187, 15, x_175);
lean_ctor_set(x_187, 16, x_176);
lean_ctor_set(x_187, 17, x_177);
lean_ctor_set(x_187, 18, x_178);
lean_ctor_set(x_187, 19, x_179);
lean_ctor_set(x_187, 20, x_180);
lean_ctor_set(x_187, 21, x_181);
lean_ctor_set(x_187, 22, x_182);
lean_ctor_set(x_187, 23, x_183);
lean_ctor_set(x_187, 24, x_184);
lean_ctor_set(x_187, 25, x_185);
lean_ctor_set_uint8(x_187, sizeof(void*)*26, x_167);
x_188 = lean_st_ref_set(x_3, x_187, x_159);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_190 = lean_st_ref_get(x_3, x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_191, 5);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_box(0);
x_195 = lean_box(0);
lean_inc(x_154);
x_196 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(x_2, x_154, x_193, x_194, x_154, x_154, x_195, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_192);
lean_dec(x_154);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_195);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_196, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_196, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_202 = x_196;
} else {
 lean_dec_ref(x_196);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Grind_activateTheorem___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_13 = l_List_reverse___rarg(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_18 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern(x_16, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_19);
{
lean_object* _tmp_1 = x_17;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_11 = x_20;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_22; 
lean_free_object(x_2);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_28 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern(x_26, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_3);
x_2 = x_27;
x_3 = x_31;
x_12 = x_30;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_activateTheorem___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_take(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_13, 12);
x_17 = l_Lean_PersistentArray_push___rarg(x_16, x_1);
lean_ctor_set(x_13, 12, x_17);
x_18 = lean_st_ref_set(x_3, x_13, x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
x_27 = lean_ctor_get(x_13, 2);
x_28 = lean_ctor_get(x_13, 3);
x_29 = lean_ctor_get(x_13, 4);
x_30 = lean_ctor_get(x_13, 5);
x_31 = lean_ctor_get(x_13, 6);
x_32 = lean_ctor_get_uint8(x_13, sizeof(void*)*26);
x_33 = lean_ctor_get(x_13, 7);
x_34 = lean_ctor_get(x_13, 8);
x_35 = lean_ctor_get(x_13, 9);
x_36 = lean_ctor_get(x_13, 10);
x_37 = lean_ctor_get(x_13, 11);
x_38 = lean_ctor_get(x_13, 12);
x_39 = lean_ctor_get(x_13, 13);
x_40 = lean_ctor_get(x_13, 14);
x_41 = lean_ctor_get(x_13, 15);
x_42 = lean_ctor_get(x_13, 16);
x_43 = lean_ctor_get(x_13, 17);
x_44 = lean_ctor_get(x_13, 18);
x_45 = lean_ctor_get(x_13, 19);
x_46 = lean_ctor_get(x_13, 20);
x_47 = lean_ctor_get(x_13, 21);
x_48 = lean_ctor_get(x_13, 22);
x_49 = lean_ctor_get(x_13, 23);
x_50 = lean_ctor_get(x_13, 24);
x_51 = lean_ctor_get(x_13, 25);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_52 = l_Lean_PersistentArray_push___rarg(x_38, x_1);
x_53 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_53, 0, x_25);
lean_ctor_set(x_53, 1, x_26);
lean_ctor_set(x_53, 2, x_27);
lean_ctor_set(x_53, 3, x_28);
lean_ctor_set(x_53, 4, x_29);
lean_ctor_set(x_53, 5, x_30);
lean_ctor_set(x_53, 6, x_31);
lean_ctor_set(x_53, 7, x_33);
lean_ctor_set(x_53, 8, x_34);
lean_ctor_set(x_53, 9, x_35);
lean_ctor_set(x_53, 10, x_36);
lean_ctor_set(x_53, 11, x_37);
lean_ctor_set(x_53, 12, x_52);
lean_ctor_set(x_53, 13, x_39);
lean_ctor_set(x_53, 14, x_40);
lean_ctor_set(x_53, 15, x_41);
lean_ctor_set(x_53, 16, x_42);
lean_ctor_set(x_53, 17, x_43);
lean_ctor_set(x_53, 18, x_44);
lean_ctor_set(x_53, 19, x_45);
lean_ctor_set(x_53, 20, x_46);
lean_ctor_set(x_53, 21, x_47);
lean_ctor_set(x_53, 22, x_48);
lean_ctor_set(x_53, 23, x_49);
lean_ctor_set(x_53, 24, x_50);
lean_ctor_set(x_53, 25, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*26, x_32);
x_54 = lean_st_ref_set(x_3, x_53, x_14);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_activateTheorem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("activated `", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_activateTheorem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_activateTheorem___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_activateTheorem___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`, ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_activateTheorem___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_activateTheorem___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 3);
x_17 = lean_ctor_get(x_1, 4);
x_18 = lean_ctor_get(x_1, 5);
x_19 = l_Lean_Meta_Grind_shareCommon(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_24 = l_List_mapM_loop___at_Lean_Meta_Grind_activateTheorem___spec__1(x_2, x_16, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_18);
lean_inc(x_25);
lean_ctor_set(x_1, 3, x_25);
lean_ctor_set(x_1, 1, x_21);
x_27 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2;
x_28 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
lean_free_object(x_19);
lean_dec(x_18);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_1, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 1);
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
x_37 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Meta_Grind_Origin_key(x_18);
lean_dec(x_18);
x_40 = l_Lean_MessageData_ofName(x_39);
x_41 = l_Lean_Meta_Grind_activateTheorem___closed__2;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_40);
lean_ctor_set(x_28, 0, x_41);
x_42 = l_Lean_Meta_Grind_activateTheorem___closed__4;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_42);
lean_ctor_set(x_19, 0, x_28);
x_43 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__1(x_25, x_23);
x_44 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__2(x_43, x_23);
x_45 = l_Lean_MessageData_ofList(x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_19);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_27, x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_1, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_51);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_50);
return x_52;
}
else
{
uint8_t x_53; 
lean_free_object(x_28);
lean_dec(x_1);
lean_dec(x_25);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_37);
if (x_53 == 0)
{
return x_37;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_37, 0);
x_55 = lean_ctor_get(x_37, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_28, 1);
lean_inc(x_57);
lean_dec(x_28);
x_58 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Meta_Grind_Origin_key(x_18);
lean_dec(x_18);
x_61 = l_Lean_MessageData_ofName(x_60);
x_62 = l_Lean_Meta_Grind_activateTheorem___closed__2;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Meta_Grind_activateTheorem___closed__4;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_64);
lean_ctor_set(x_19, 0, x_63);
x_65 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__1(x_25, x_23);
x_66 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__2(x_65, x_23);
x_67 = l_Lean_MessageData_ofList(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_19);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_27, x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_59);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_1, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_73);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_1);
lean_dec(x_25);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_75 = lean_ctor_get(x_58, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_58, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_77 = x_58;
} else {
 lean_dec_ref(x_58);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_free_object(x_19);
lean_dec(x_21);
lean_free_object(x_1);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_24);
if (x_79 == 0)
{
return x_24;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_24, 0);
x_81 = lean_ctor_get(x_24, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_24);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_19, 0);
x_84 = lean_ctor_get(x_19, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_19);
x_85 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_86 = l_List_mapM_loop___at_Lean_Meta_Grind_activateTheorem___spec__1(x_2, x_16, x_85, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_18);
lean_inc(x_87);
lean_ctor_set(x_1, 3, x_87);
lean_ctor_set(x_1, 1, x_83);
x_89 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2;
x_90 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_89, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_88);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_87);
lean_dec(x_18);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_box(0);
x_95 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_1, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_93);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
x_98 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_Lean_Meta_Grind_Origin_key(x_18);
lean_dec(x_18);
x_101 = l_Lean_MessageData_ofName(x_100);
x_102 = l_Lean_Meta_Grind_activateTheorem___closed__2;
if (lean_is_scalar(x_97)) {
 x_103 = lean_alloc_ctor(7, 2, 0);
} else {
 x_103 = x_97;
 lean_ctor_set_tag(x_103, 7);
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = l_Lean_Meta_Grind_activateTheorem___closed__4;
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__1(x_87, x_85);
x_107 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__2(x_106, x_85);
x_108 = l_Lean_MessageData_ofList(x_107);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_89, x_111, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_99);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_1, x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_114);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_113);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_97);
lean_dec(x_1);
lean_dec(x_87);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_116 = lean_ctor_get(x_98, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_98, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_118 = x_98;
} else {
 lean_dec_ref(x_98);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_83);
lean_free_object(x_1);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_120 = lean_ctor_get(x_86, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_86, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_122 = x_86;
} else {
 lean_dec_ref(x_86);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_124 = lean_ctor_get(x_1, 0);
x_125 = lean_ctor_get(x_1, 1);
x_126 = lean_ctor_get(x_1, 2);
x_127 = lean_ctor_get(x_1, 3);
x_128 = lean_ctor_get(x_1, 4);
x_129 = lean_ctor_get(x_1, 5);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_1);
x_130 = l_Lean_Meta_Grind_shareCommon(x_125, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_135 = l_List_mapM_loop___at_Lean_Meta_Grind_activateTheorem___spec__1(x_2, x_127, x_134, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_132);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
lean_inc(x_129);
lean_inc(x_136);
x_138 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_138, 0, x_124);
lean_ctor_set(x_138, 1, x_131);
lean_ctor_set(x_138, 2, x_126);
lean_ctor_set(x_138, 3, x_136);
lean_ctor_set(x_138, 4, x_128);
lean_ctor_set(x_138, 5, x_129);
x_139 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2;
x_140 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_139, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_137);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_136);
lean_dec(x_133);
lean_dec(x_129);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_box(0);
x_145 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_138, x_144, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_143);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_147 = x_140;
} else {
 lean_dec_ref(x_140);
 x_147 = lean_box(0);
}
x_148 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_146);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_150 = l_Lean_Meta_Grind_Origin_key(x_129);
lean_dec(x_129);
x_151 = l_Lean_MessageData_ofName(x_150);
x_152 = l_Lean_Meta_Grind_activateTheorem___closed__2;
if (lean_is_scalar(x_147)) {
 x_153 = lean_alloc_ctor(7, 2, 0);
} else {
 x_153 = x_147;
 lean_ctor_set_tag(x_153, 7);
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l_Lean_Meta_Grind_activateTheorem___closed__4;
if (lean_is_scalar(x_133)) {
 x_155 = lean_alloc_ctor(7, 2, 0);
} else {
 x_155 = x_133;
 lean_ctor_set_tag(x_155, 7);
}
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__1(x_136, x_134);
x_157 = l_List_mapTR_loop___at_Lean_Meta_Grind_mkEMatchTheoremCore___spec__2(x_156, x_134);
x_158 = l_Lean_MessageData_ofList(x_157);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6;
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_139, x_161, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_149);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_138, x_163, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_164);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_163);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_147);
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_133);
lean_dec(x_129);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_166 = lean_ctor_get(x_148, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_148, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_168 = x_148;
} else {
 lean_dec_ref(x_148);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_170 = lean_ctor_get(x_135, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_135, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_172 = x_135;
} else {
 lean_dec_ref(x_135);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_is_matcher(x_14, x_1);
x_16 = lean_box(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_is_matcher(x_19, x_1);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
lean_dec(x_7);
x_19 = lean_array_uget(x_4, x_6);
x_20 = 0;
x_21 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_22 = l_Lean_Meta_Grind_mkEMatchEqTheorem(x_19, x_20, x_21, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_25 = l_Lean_Meta_Grind_activateTheorem(x_23, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 1;
x_28 = lean_usize_add(x_6, x_27);
x_29 = lean_box(0);
x_6 = x_28;
x_7 = x_29;
x_16 = x_26;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_13 = lean_st_ref_take(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 5);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 6);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_14, sizeof(void*)*26);
x_24 = lean_ctor_get(x_14, 7);
lean_inc(x_24);
x_25 = lean_ctor_get(x_14, 8);
lean_inc(x_25);
x_26 = lean_ctor_get(x_14, 9);
lean_inc(x_26);
x_27 = lean_ctor_get(x_14, 10);
lean_inc(x_27);
x_28 = lean_ctor_get(x_14, 11);
lean_inc(x_28);
x_29 = lean_ctor_get(x_14, 12);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 13);
lean_inc(x_30);
x_31 = lean_ctor_get(x_14, 14);
lean_inc(x_31);
x_32 = lean_ctor_get(x_14, 15);
lean_inc(x_32);
x_33 = lean_ctor_get(x_14, 16);
lean_inc(x_33);
x_34 = lean_ctor_get(x_14, 17);
lean_inc(x_34);
x_35 = lean_ctor_get(x_14, 18);
lean_inc(x_35);
x_36 = lean_box(0);
lean_inc(x_1);
x_37 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_35, x_1, x_36);
x_38 = lean_ctor_get(x_14, 19);
lean_inc(x_38);
x_39 = lean_ctor_get(x_14, 20);
lean_inc(x_39);
x_40 = lean_ctor_get(x_14, 21);
lean_inc(x_40);
x_41 = lean_ctor_get(x_14, 22);
lean_inc(x_41);
x_42 = lean_ctor_get(x_14, 23);
lean_inc(x_42);
x_43 = lean_ctor_get(x_14, 24);
lean_inc(x_43);
x_44 = lean_ctor_get(x_14, 25);
lean_inc(x_44);
lean_dec(x_14);
x_45 = lean_alloc_ctor(0, 26, 1);
lean_ctor_set(x_45, 0, x_16);
lean_ctor_set(x_45, 1, x_17);
lean_ctor_set(x_45, 2, x_18);
lean_ctor_set(x_45, 3, x_19);
lean_ctor_set(x_45, 4, x_20);
lean_ctor_set(x_45, 5, x_21);
lean_ctor_set(x_45, 6, x_22);
lean_ctor_set(x_45, 7, x_24);
lean_ctor_set(x_45, 8, x_25);
lean_ctor_set(x_45, 9, x_26);
lean_ctor_set(x_45, 10, x_27);
lean_ctor_set(x_45, 11, x_28);
lean_ctor_set(x_45, 12, x_29);
lean_ctor_set(x_45, 13, x_30);
lean_ctor_set(x_45, 14, x_31);
lean_ctor_set(x_45, 15, x_32);
lean_ctor_set(x_45, 16, x_33);
lean_ctor_set(x_45, 17, x_34);
lean_ctor_set(x_45, 18, x_37);
lean_ctor_set(x_45, 19, x_38);
lean_ctor_set(x_45, 20, x_39);
lean_ctor_set(x_45, 21, x_40);
lean_ctor_set(x_45, 22, x_41);
lean_ctor_set(x_45, 23, x_42);
lean_ctor_set(x_45, 24, x_43);
lean_ctor_set(x_45, 25, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*26, x_23);
x_46 = lean_st_ref_set(x_4, x_45, x_15);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_48 = lean_get_match_equations_for(x_1, x_8, x_9, x_10, x_11, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(0);
x_53 = lean_array_size(x_51);
x_54 = 0;
x_55 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__2(x_2, x_51, x_52, x_51, x_53, x_54, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_50);
lean_dec(x_51);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_36);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_36);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_48);
if (x_64 == 0)
{
return x_48;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_48, 0);
x_66 = lean_ctor_get(x_48, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_48);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 18);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_17, x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_13);
x_19 = lean_box(0);
x_20 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__1(x_1, x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_ctor_get(x_22, 18);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_24, x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__1(x_1, x_2, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_13);
x_14 = l_Lean_Meta_isMatcher___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__1(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_box(0);
x_25 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__2(x_13, x_2, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_12);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Meta_Grind_getConfig___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*6);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__3(x_1, x_2, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_4, x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
x_17 = lean_array_uget(x_3, x_4);
x_18 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_17);
x_19 = l_Lean_Meta_Grind_internalize(x_17, x_2, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_1);
x_21 = l_Lean_Meta_Grind_registerParent(x_1, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_4, x_24);
x_4 = x_25;
x_6 = x_22;
x_15 = x_23;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_15);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Meta_Grind_mkENodeCore(x_1, x_12, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_15 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_array_get_size(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_23 = l_Lean_Meta_Grind_propagateUp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_26 = l_Lean_Meta_Grind_internalize(x_19, x_2, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_28 = l_Lean_Meta_mkEqRefl(x_1, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_Grind_pushEqCore(x_1, x_19, x_29, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_23, 0);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_23);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_20, x_20);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_45 = l_Lean_Meta_Grind_propagateUp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_48 = l_Lean_Meta_Grind_internalize(x_19, x_2, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_50 = l_Lean_Meta_mkEqRefl(x_1, x_7, x_8, x_9, x_10, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Meta_Grind_pushEqCore(x_1, x_19, x_51, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_50, 0);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_50);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_48);
if (x_58 == 0)
{
return x_48;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_48, 0);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_48);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_45);
if (x_62 == 0)
{
return x_45;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_45, 0);
x_64 = lean_ctor_get(x_45, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_45);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; 
x_66 = 0;
x_67 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_68 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_69 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___spec__1(x_1, x_2, x_18, x_66, x_67, x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_18);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_71 = l_Lean_Meta_Grind_propagateUp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_19);
x_74 = l_Lean_Meta_Grind_internalize(x_19, x_2, x_73, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_76 = l_Lean_Meta_mkEqRefl(x_1, x_7, x_8, x_9, x_10, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Meta_Grind_pushEqCore(x_1, x_19, x_77, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_78);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_76);
if (x_80 == 0)
{
return x_76;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_76, 0);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_76);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_74);
if (x_84 == 0)
{
return x_74;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_74, 0);
x_86 = lean_ctor_get(x_74, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_74);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_71);
if (x_88 == 0)
{
return x_71;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_71, 0);
x_90 = lean_ctor_get(x_71, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_71);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_69);
if (x_92 == 0)
{
return x_69;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_69, 0);
x_94 = lean_ctor_get(x_69, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_69);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_15);
if (x_96 == 0)
{
return x_15;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_15, 0);
x_98 = lean_ctor_get(x_15, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_15);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___spec__1(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_internalize___spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Grind_internalize___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_internalize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_internalize___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_internalize___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_internalize___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_internalize___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_internalize___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_PersistentHashMap_containsAtAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_activateTheorem___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_activateTheorem___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_isMatcher___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___spec__2(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addMatchEqns___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizeMatchCond___spec__1(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
return x_18;
}
}
lean_object* initialize_Init_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Beta(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Internalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchEqsExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Canon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Beta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__1();
l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_findEntryAux___at_Lean_Meta_Grind_addCongrTable___spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Grind_addCongrTable___spec__5___closed__1);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__1);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__2 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__2);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__3 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__3);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__4 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__4);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__5 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__5);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__6);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__7 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__7);
l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__8 = _init_l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___lambda__2___closed__8);
l_Lean_Meta_Grind_addCongrTable___closed__1 = _init_l_Lean_Meta_Grind_addCongrTable___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___closed__1);
l_Lean_Meta_Grind_addCongrTable___closed__2 = _init_l_Lean_Meta_Grind_addCongrTable___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___closed__2);
l_Lean_Meta_Grind_addCongrTable___closed__3 = _init_l_Lean_Meta_Grind_addCongrTable___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___closed__3);
l_Lean_Meta_Grind_addCongrTable___closed__4 = _init_l_Lean_Meta_Grind_addCongrTable___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___closed__4);
l_Lean_Meta_Grind_addCongrTable___closed__5 = _init_l_Lean_Meta_Grind_addCongrTable___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___closed__5);
l_Lean_Meta_Grind_addCongrTable___closed__6 = _init_l_Lean_Meta_Grind_addCongrTable___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_addCongrTable___closed__6);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_addSplitCandidate___closed__3);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__3);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__4);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__5);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__6);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__7);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__8);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__9);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__10);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__11);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes___closed__12);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_forbiddenSplitTypes);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__1___closed__4);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___lambda__4___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__3);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__4);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__5);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__6);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__7);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__8);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_pushCastHEqs___closed__9);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__1);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__2);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__3);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_preprocessGroundPattern___closed__4);
l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_internalizePattern___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_Grind_internalize___spec__2___closed__4);
l_Lean_Meta_Grind_internalize___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_internalize___lambda__2___closed__1);
l_Lean_Meta_Grind_internalize___lambda__2___closed__2 = _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_internalize___lambda__2___closed__2);
l_Lean_Meta_Grind_internalize___lambda__2___closed__3 = _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_internalize___lambda__2___closed__3);
l_Lean_Meta_Grind_internalize___lambda__2___closed__4 = _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_internalize___lambda__2___closed__4);
l_Lean_Meta_Grind_internalize___lambda__2___closed__5 = _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_internalize___lambda__2___closed__5);
l_Lean_Meta_Grind_internalize___lambda__2___closed__6 = _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_internalize___lambda__2___closed__6);
l_Lean_Meta_Grind_internalize___lambda__2___closed__7 = _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_internalize___lambda__2___closed__7);
l_Lean_Meta_Grind_internalize___lambda__2___closed__8 = _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_internalize___lambda__2___closed__8);
l_Lean_Meta_Grind_internalize___lambda__2___closed__9 = _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_internalize___lambda__2___closed__9);
l_Lean_Meta_Grind_internalize___lambda__2___closed__10 = _init_l_Lean_Meta_Grind_internalize___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_internalize___lambda__2___closed__10);
l_Lean_Meta_Grind_internalize___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_internalize___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_internalize___lambda__3___closed__1);
l_Lean_Meta_Grind_internalize___lambda__3___closed__2 = _init_l_Lean_Meta_Grind_internalize___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_internalize___lambda__3___closed__2);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___lambda__1___closed__1);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__1 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__1);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__2);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__3 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__3);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__4);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__5 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__5();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__5);
l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__6 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__6();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_Tactic_Grind_Internalize_0__Lean_Meta_Grind_activateTheoremPatterns___spec__5___closed__6);
l_Lean_Meta_Grind_activateTheorem___closed__1 = _init_l_Lean_Meta_Grind_activateTheorem___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_activateTheorem___closed__1);
l_Lean_Meta_Grind_activateTheorem___closed__2 = _init_l_Lean_Meta_Grind_activateTheorem___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_activateTheorem___closed__2);
l_Lean_Meta_Grind_activateTheorem___closed__3 = _init_l_Lean_Meta_Grind_activateTheorem___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_activateTheorem___closed__3);
l_Lean_Meta_Grind_activateTheorem___closed__4 = _init_l_Lean_Meta_Grind_activateTheorem___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_activateTheorem___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
