# LocalAuto1 lane handoff (2026-10-08 session)

## State on disk
- `lean/Kepler/Text/LocalAuto1.lean` (2823 lines): **compiles green** via
  `lake env lean /tmp/la1_probe.lean` (probe = whole file copy; exit=0,
  only `declaration uses 'sorry'` warnings).
- Sorry warnings: **82** (down from 85 at session start; grep "sorry" 88,
  of which 1 is the TBRMXRZ1 NEEDS comment). Predecessor had taken 96 -> 90.
- This session discharged **3**: `EQTTNZI2_concl`, `PEDSLGV1_concl`,
  `PEDSLGV2_concl` (+ ~330 lines of private `la1*` toolkit).
- New private kit (all before `YXIONXL3`): `la1shift_inj/_rho/_surj/_back`,
  `la1setSum_image/_congr/_shift`, `la1tau3_cyc/_cyc2`, `la1periodic2_mul`,
  `la1range_shift` (needs `hk : 0 < k` + `hxper`), `la1shift_ncard`,
  `la1isScs_propEqu` (COMPLETE, compiles), plus earlier-session
  `la1periodic_mul/_mod`, `la1csAdj_diag6`, `la1bbindexMin_le/_attained`,
  `la1bbprime_taustar_eq`, `la1psort_*`, `la1minNum_spec`.

## Next run: finish `YXIONXL3_concl` (stage 2 sketch, ~250 lines)
`scsArrowV39 {s} {scsPropEquV39 s i}` needs (1) `isScsV39 (propEqu s i)` — DONE
as `la1isScs_propEqu`; (2) MMs transport. Remaining lemmas, all mechanical:
1. `la1shiftBBs`: `BBs s x -> BBs (propEqu s i) (fun m => x (i+m))`. Ranges via
   `la1range_shift hk hxper` (also for edge/face funs: `Periodic (fun m => {x m,
   x (m+1)}) k` via `rw [hp m, hp (m+1)]` after assoc-juggling `m+k+1 = (m+1)+k`);
   bounds direct (`t.a j j' = s.a (i+j) (i+j')` definitionally).
2. Backward BBs with rho-shift `fun m => y ((m + k - i % k) % k)`: bounds via
   `la1periodic2_mod` + `la1shift_rho` (gives `(i + rho m) % k = m`); ranges via
   `la1shift_back`-based range equality; periodicity of rho-shift needs
   `((m+k) + (k - i%k)) % k = (m + (k - i%k)) % k` (assoc + add_mod_right).
3. `la1shift_taustar`: `Periodic x k -> taustar (propEqu s i) (shift x) = taustar s x`.
   tauFun branch: `la1range_shift` x3. k=3 branch: tau3-cyclic (`la1tau3_cyc`,
   `la1tau3_cyc2`, both close by `ring`) + rcases on `i % 3` with
   `la1periodic_mul hx3`. dsv branch: J-sums via `la1setSum_shift`
   (hiff via `la1periodic2_mul h12` + `hsplit`-style sums; hfg via periodic x),
   ear-flags via (4).
4. `la1isEar_propEqu (s i his) : isEar (propEqu s i) <-> isEar s`. ~120 lines.
   Forward: unadorned transport via rho + `la1periodic_mod`/`la1periodic2_mod`;
   `isEar t` gives `t.b i i = 0` etc.; J-singleton `{j|j<3 & t.J j (j+1)} = {i0}`
   transports to `{m|j<3 & s.J m (m+1)} = {(i+i0)%k}` (sigma-bijection);
   slot values via `la1periodic2_mul`; the `hoth` clause at `j := rho3 m`.
   Backward mirrors with `i0' := rho3 i0`.
5. `la1shift_BBindex`: `{j | j < k & t.a j (j+1) = dist (w j) (w (j+1))}.ncard
   = {m | ...s.a m (m+1) = dist (x m) (x (m+1))}.ncard` via `la1shift_ncard`
   (hiff: `la1periodic2_mul h8` + dist-periodicity of x). BBindexMin:
   `la1bbindexMin_le` + `la1bbindexMin_attained` min-element transported
   both directions (MXQTIED pattern).
6. Assembly: `BBprime` transport (minimality: y in BBs s' -> rho-shift y in
   BBs s -> `hmin`; taustar equality applied both directions — note
   `shift (rho-shift y) = y` needs `la1shift_back` + `la1periodic_mod`),
   then MMs clauses direct.

## Gotchas learned this session (saves ~8 probe rounds)
- `Nat.mod_mod` (not `Nat.mod_mod_eq`); `Nat.ModEq.add_left_cancel'`.
- `Set.Finite.image f hB` (f first); `Set.Finite.toFinset_image f hB hfin`
  needs `[DecidableEq]` -> `haveI := Classical.decEq α`.
- Anonymous `⟨...⟩` FLATTENS nested notation: ascribe intermediate
  conjunctions with `have` (e.g. `have hvB2 : v ∈ BBprime2V39 t := ⟨hvBT, hidxT⟩`).
- `Set.Nonempty` goals from `... ≠ ∅`: close via
  `Set.nonempty_iff_ne_empty.mp ⟨v, hv⟩` (`.mp`, not `.mpr`).
- `nth_rewrite` does not auto-close rfl goals; append `rfl`.
- `rw` inside `by`-blocks under an unfixed iff-parameter: ascribe the hiff
  with concrete types first (P/Q-mvars otherwise leak as `?m`).
- omega treats `%`/`/` by variables as atoms ONLY with bounding hyps given
  (`Nat.mod_lt`); products of atoms are nonlinear -> `linarith [hsplit j]`.
- Elementwise `hset : {j | P (i+j)} = {j | P j}` is FALSE; only ncard-equality
  (`la1shift_ncard`) is available — do NOT re-add that lemma.
- Other lanes run `lake build` in the same tree: transient missing oleans
  (PackingAuto10/15, SphereKit) — wait ~30 s and re-probe; never build.

## Residuals (87 proof-sorries)
- TBRMXRZ1_concl: FALSE as stated (NEEDS comment at line ~1792, statement-fix lane).
- Cluster geometry-deep (unfixable mechanically): ZITHLQN/EAPGLE/XWITCCN*/AYQJTMD,
  JKQEWGV1-3, HFNXPZA, MHAEYJN, ZLZTHIC, VPWSHTO, UAGHHBM, ODXLSTCv2, IMJXPHRv2,
  NUXCOEAv2, PQCSXWG1/2, EYYPQDW1-3, FEKTYIY, AURSIPD, PPBTYDQ, SYNQIWN,
  XWNHLMD (under-hypothesized), OIQKKEP, AXJRPNC, RRCWNSJ...VASYYAU,
  CUXVZOZ/CJBDXXN (antecedent is a sorry-Prop), WKEIDFT (psort classes
  non-cancellable), GSXRFWM/WGDHPPI.
- Concrete-arrow cluster (~24): blocked ONLY by MMs-nonemptiness of targets
  (no realization-existence kit in this file).PEDSLGV1/2-style transports
  work; the source-realization existence lives in the Local Fan chapter.
- YXIONXL1: likely needs extra hypothesis (dsv-flag monotonicity);
  YXIONXL2 (opp) analogous to YXIONXL3 but with reversal map.
