Add LoadPath "../general".

Require Export require_general.
Require Export LNS.
Require Export require_structural.

Set Implicit Arguments.


Definition can_gen_cut {V : Set}
  (rules : rlsT (@LNS V)) ns1 ns2 :=
  forall G1 G2 G3 s1 s2 (d : dir) Γ Δ1 Δ2 Σ1 Σ2 Π A,
    ns1 = G1 ++ [(s1, d)] -> s1 = pair Γ (Δ1++[A]++Δ2) ->
    ns2 = G2 ++ [(s2, d)] -> s2 = pair (Σ1++[A]++Σ2) Π ->
    merge G1 G2 G3 ->
    struct_equiv_str G1 G2 ->
    pf rules (G3 ++ [(Γ++Σ1++Σ2, Δ1++Δ2++Π, d)]).

Definition can_gen_cut_simpl {V : Set}
  (rules : rlsT (@LNS V)) ns1 ns2 :=
  forall G s1 s2 (d : dir) Γ1 Γ2 Δ1 Δ2 A,
    ns1 = G ++ [(s1, d)] -> s1 = pair Γ1 (Δ1++[A]) ->
    ns2 = G ++ [(s2, d)] -> s2 = pair (Γ2++[A]) Δ2 ->
    pf rules (G ++ [(Γ1++Γ2, Δ1++Δ2, d)]).
