load "AutSplit.m";

// ---------------------------------------------------------------------------
// RatESSolve: Algorithm 2
//
// Input:  E -- EllipticCurve over FunctionField(k) where k is a number field
//              (or k = Q).  Both short and long Weierstrass are accepted.
// Output: rk      -- Mordell-Weil rank (integer)
//         K       -- field of definition of the sections (number field or Q)
//         Aut     -- Gal(K/Q) as a permutation group
//         Sections-- sequence of r MW generators as sequences of length 2 over K
//                    (affine coords [x(t), y(t)] with coefficients in K)
//         TorsPts -- torsion subgroup points (same format, or O)
//         IrrReps -- irreducible Q-rational constituents of the G-module
//         Chars   -- corresponding rational characters (from RationalCharacterTable)
// ---------------------------------------------------------------------------
function RatESSolve(E : Verbose := true, UsePD := true)

    // ------------------------------------------------------------------
    // Step 1: build the ideal from the section ansatz
    //   x(t) = s1*t^2 + s2*t + s3
    //   y(t) = s4*t^3 + s5*t^2 + s6*t + s7
    // Substitute into the (long) Weierstrass equation and collect by t-degree.
    // ------------------------------------------------------------------
    ai := aInvariants(E);  // [a1, a2, a3, a4, a6] in k(t)
    FF := Parent(ai[1]);   // FunctionField(k)
    t  := FF.1;
    k  := BaseRing(FF);    // number field (or Q)
    UsePD:=true;
    // BaseRing(FF) can return Q even when FF = FunctionField(K) for a number field K
    // in some Magma builds.  Detect the true coefficient field by inspecting the
    // a-invariant numerators directly, without calling Coefficients on potentially
    // bad types.
    if Type(k) eq FldRat then
        for _f in ai do
            _num := Numerator(_f);
            if ISA(Type(_num), RngUPolElt) then
                for _c in Coefficients(_num) do
                    if not IsCoercible(RationalField(), _c) then
                        k := Parent(_c); break;
                    end if;
                end for;
            elif not IsCoercible(RationalField(), _num) then
                k := Parent(_num);
            end if;
            if Type(k) ne FldRat then break; end if;
        end for;
    end if;

    // ------------------------------------------------------------------
    // Method dispatch: Options A + B choose between primary decomposition
    // and Points(E_K, K(t)).  Threshold: < 5 on both proxies.
    //
    // Option B (fast, before any decomposition): exact rank via Shioda-Tate
    //   rank = 8 - Σ_v (m_v - 1) using LocalInformation(E) for k = Q.
    //   For k != Q the Points path is unconditionally disabled, so a rough
    //   discriminant-based bound is used there instead.
    //   disc_E (in k[t]) is computed here and reused in Step 5b.
    // ------------------------------------------------------------------
    // Compute disc_E in k[t] from the Weierstrass a-invariants directly.
    // Magma's Discriminant(E) and Numerator() can return wrong types for E over
    // FunctionField(k) with k a number field.  The b-invariant formula avoids this;
    // extraction via Coefficients(Numerator(ai[j])) uses the same pattern as LiftToRt.
    _Rk<_tk> := PolynomialRing(k);
    function _ff_to_Rk(f)
        // Numerator() returns a bare scalar (FldRatElt or FldNumElt) rather than a
        // RngUPolElt for constant elements of FunctionField(k).  ISA(Type, RngUPolElt)
        // detects this.  For scalars: k=Q uses direct coercion (k![seq] is invalid for
        // FldRat); k a number field uses Eltseq to bypass FldNum object-identity mismatches
        // that make IsCoercible(k, num) fail even when the abstract field is the same.
        if IsZero(f) then return _Rk!0; end if;
        num := Numerator(f);
        if not ISA(Type(num), RngUPolElt) then
            // k is now correct (fixed at function entry); direct coercion works.
            return _Rk!(k!num);
        end if;
        cf := Coefficients(num);
        if #cf eq 0 then return _Rk!0; end if;
        return &+[(k!cf[i]) * _tk^(i-1) : i in [1..#cf]];
    end function;
    _a1r := _ff_to_Rk(ai[1]); _a2r := _ff_to_Rk(ai[2]); _a3r := _ff_to_Rk(ai[3]);
    _a4r := _ff_to_Rk(ai[4]); _a6r := _ff_to_Rk(ai[5]);
    _b2  := _a1r^2 + 4*_a2r;
    _b4  := _a1r*_a3r + 2*_a4r;
    _b6  := _a3r^2 + 4*_a6r;
    _b8  := _a1r^2*_a6r - _a1r*_a3r*_a4r + 4*_a2r*_a6r + _a2r*_a3r^2 - _a4r^2;
    disc_E := -_b2^2*_b8 - 8*_b4^3 - 27*_b6^2 + 9*_b2*_b4*_b6;

    // Option B: exact Shioda-Tate rank for rational elliptic surfaces.
    // rho = NS rank of the surface = 2 + Σ_v (m_v - 1);
    // MW rank = 10 - rho  (equivalently 8 - Σ_v (m_v - 1)).
    // KodairaSymbols works over any base field k.
    rho_st := 2;
    H_kod  := KodairaSymbols(E);
    for i in [1..#H_kod] do
        rho_st +:= NumberOfComponents(H_kod[i][1]) - 1;
    end for;
    shioda_rank := Max(0, 10 - rho_st);
    if Verbose then
        printf "Option B: %o bad fiber(s), Shioda-Tate rank = %o.\n", #H_kod, shioda_rank;
    end if;

    // Method selection: for k = Q use the rank estimate to gate the fast Points path;
    // for k != Q the Variety path is always the default (overridden only by UsePD).
    if Type(k) eq FldRat then
        use_points := shioda_rank lt 5;
    else
        use_points := not UsePD;
    end if;
    if Verbose then
        printf "Option B: %o.\n",
            use_points select "→ Points/Variety path" else "→ BackSubAll/PD path";
    end if;

    // Polynomial ring in the 7 section coefficients, over k
    R7<s1,s2,s3,s4,s5,s6,s7> := PolynomialRing(k, 7, "lex");
    Rt := PolynomialRing(R7);   // R7[t]
    tt := Rt.1;

    // Lift a_i(t) into Rt (coefficients now in R7)
    function LiftToRt(f)
        // f is in k(t); pull numerator coefficients into R7[t].
        // Same scalar-dispatch as _ff_to_Rk: ISA + Type(k) branch.
        if IsZero(f) then return Rt!0; end if;
        num := Numerator(f);
        if not ISA(Type(num), RngUPolElt) then
            return R7!(k!num);
        end if;
        cf := Coefficients(num);
        if #cf eq 0 then return Rt!0; end if;
        return &+[R7!(k!cf[i]) * tt^(i-1) : i in [1..#cf]];
    end function;

    a1 := LiftToRt(ai[1]);
    a2 := LiftToRt(ai[2]);
    a3 := LiftToRt(ai[3]);
    a4 := LiftToRt(ai[4]);
    a6 := LiftToRt(ai[5]);

    X := s1*tt^2 + s2*tt + s3;
    Y := s4*tt^3 + s5*tt^2 + s6*tt + s7;

    // Long Weierstrass: y^2 + a1*x*y + a3*y - x^3 - a2*x^2 - a4*x - a6 = 0
    WEq := Y^2 + a1*X*Y + a3*Y - X^3 - a2*X^2 - a4*X - a6;

    // Collect coefficients in t; each must vanish
    coeffs_t := Coefficients(WEq);
    I := ideal<R7 | coeffs_t>;

    if Verbose then printf "Step 1: Ideal formed (%o generators).\n", #coeffs_t; end if;

    // ------------------------------------------------------------------
    // Step 2: extract univariates and build K.
    //
    // GB path (UsePD=false, k=Q — the default): compute the lex Gröbner basis
    // of I directly, bypassing PrimaryDecomposition.  The univariate in the
    // last lex-variable drives Option A.  If est_deg < 5 and use_points=true,
    // Variety(I_K) finds all sections; otherwise BackSubAll-from-GB iterates
    // roots of poly_fast through the remaining GB elements.
    //
    // PD path (UsePD=true, k != Q, or GB found no univariate): primary decompose,
    // then extract per-component univariates.  For k != Q this feeds SplitAutGrp
    // to find the splitting field K; sections are then recovered via Variety(I_K)
    // (default) or BackSubAll (UsePD=true).
    // ------------------------------------------------------------------
    Qx<x> := PolynomialRing(RationalField());
    comp_data     := [];
    seen_polys    := [];
    comp_for_poly := [];
    extra_seen    := [];

    poly_fast     := false;   // univariate polynomial for fast path SplitAutGrp
    fast_extra    := [];      // extra univariates from non-linear GB elements (fast path)
    gb_path_taken := false;   // set true when GB path finds a usable univariate

    if not UsePD and Type(k) eq FldRat then
        if Verbose then printf "Step 2 (fast): lex Gröbner basis (skipping primary decomp)...\n"; end if;
        GB_fast := GroebnerBasis(I);
        // Rank-0 check: if the GB collapses to {1}, the variety is empty.
        if exists{g : g in GB_fast | g eq R7!1} then
            if Verbose then printf "Rank 0 detected: no sections (GB path).\n"; end if;
            Qfield := RationalField(); trivGrp := SymmetricGroup(1);
            return 0, Qfield, trivGrp, [], [], [], [];
        end if;
        uni_fast := false; udeg_fast := 0; uvar_fast := 0;
        for g in GB_fast do
            vars_g := {};
            for m in Monomials(g) do
                ev := Exponents(m);
                for i in [1..7] do if ev[i] ne 0 then Include(~vars_g, i); end if; end for;
            end for;
            if #vars_g eq 1 and Degree(g) gt udeg_fast then
                uni_fast := g; udeg_fast := Degree(g); uvar_fast := Rep(vars_g);
            end if;
        end for;

        if uni_fast cmpne false then
            cf := [MonomialCoefficient(uni_fast, R7.uvar_fast^i) : i in [0..udeg_fast]];
            poly_fast := Polynomial(RationalField(), [RationalField()!c : c in cf]);
            poly_fast := poly_fast div GCD(poly_fast, Derivative(poly_fast));
            est_deg := Degree(poly_fast);
            gb_path_taken := true;
            if Verbose then
                printf "Step 2 (fast): univariate degree = %o in s%o (Option A est_deg = %o).\n",
                    udeg_fast, uvar_fast, est_deg;
            end if;
            if est_deg ge 5 then
                use_points := false;
                if Verbose then printf "  -> est_deg >= 5; BackSubAll-from-GB will be used.\n"; end if;
            end if;
            // Scan for non-linear non-univariate GB elements in other variables.
            // Resultant against uni_fast yields a univariate in s_i whose splitting
            // field extends K.  Needed for both Variety and BackSubAll-from-GB.
            for g in GB_fast do
                lv_g := Min([i : i in [1..7] | Exponents(LeadingMonomial(g))[i] ne 0]);
                if lv_g eq uvar_fast then continue; end if;
                deg_g_lv := Max([Exponents(m)[lv_g] : m in Monomials(g)]);
                if deg_g_lv le 1 then continue; end if;
                res := Resultant(g, uni_fast, R7.uvar_fast);
                if IsZero(res) then continue; end if;
                vars_res := {};
                for m in Monomials(res) do
                    ev := Exponents(m);
                    for i in [1..7] do if ev[i] ne 0 then Include(~vars_res, i); end if; end for;
                end for;
                if not (#vars_res eq 1 and lv_g in vars_res) then continue; end if;
                deg_res := Max([Exponents(m)[lv_g] : m in Monomials(res)]);
                cf_res := [MonomialCoefficient(res, R7.lv_g^d) : d in [0..deg_res]];
                ep := Polynomial(RationalField(), [RationalField()!c : c in cf_res]);
                ep := ep div GCD(ep, Derivative(ep));
                for ep_fac in Factorization(ep) do
                    ep_f := ep_fac[1];
                    if Degree(ep_f) ge 2 and not exists{p : p in fast_extra | p eq ep_f} then
                        Append(~fast_extra, ep_f);
                    end if;
                end for;
            end for;
            if Verbose and #fast_extra gt 0 then
                printf "  -> %o extra polynomial(s) from non-linear GB element(s).\n", #fast_extra;
            end if;
        else
            if Verbose then
                printf "  -> No univariate in lex GB; falling back to primary decomp.\n";
            end if;
        end if;
    end if;

    if not gb_path_taken then
        // Full path: primary decompose, then extract per-component univariates.
        // Runs when UsePD=true, k != Q, or GB found no univariate.
        if Verbose then printf "Step 2: Primary decomposition...\n"; end if;
        PD := PrimaryDecomposition(I);

        non_triv := [Q : Q in PD | Dimension(Q) eq 0];

        if #non_triv eq 0 then
            if Verbose then printf "Rank 0 detected: no sections.\n"; end if;
            Qfield := RationalField();
            trivGrp := SymmetricGroup(1);
            return 0, Qfield, trivGrp, [], [], [], [];
        end if;

        // For k != Q: precompute the bivariate ring and kdef polynomial used to eliminate
        // the k-generator via resultant.  For f(x) ∈ k[x], Res_β(m(β), f(x,β)) = norm over Q.
        if Type(k) ne FldRat then
            _Qxb<_xv, _yv> := PolynomialRing(Rationals(), 2);
            _dk := Degree(k);
            _kdef_y := &+[(Rationals()!Coefficient(DefiningPolynomial(k),_i))*_yv^_i
                          : _i in [0..Degree(DefiningPolynomial(k))]];
        end if;

        for Q in non_triv do
            GB := GroebnerBasis(Q);
            uni := false; deg_uni := 0; uni_var := 0;
            for g in GB do
                vars_used := {};
                for m in Monomials(g) do
                    ev := Exponents(m);
                    for i in [1..7] do
                        if ev[i] ne 0 then Include(~vars_used, i); end if;
                    end for;
                end for;
                if #vars_used eq 1 and Degree(g) gt deg_uni then
                    uni := g; deg_uni := Degree(g); uni_var := Rep(vars_used);
                end if;
            end for;
            if uni cmpeq false then continue; end if;

            cf := [MonomialCoefficient(uni, R7.uni_var^i) : i in [0..deg_uni]];
            if Type(k) eq FldRat then
                poly := Polynomial(RationalField(), [RationalField()!c : c in cf]);
            else
                // Absolute minimal polynomial over Q via resultant: eliminate k.1 = β.
                // Res_β(m(β), f(x, β)) where f is the univariate lifted to Q[x, β].
                _fk  := Polynomial(k, [k!c : c in cf]);
                _fxb := &+[(&+[(_Qxb!(Rationals()!Eltseq(Coefficient(_fk,_i))[_j]))*_yv^(_j-1)
                               : _j in [1.._dk]]) * _xv^_i : _i in [0..Degree(_fk)]];
                _res := Resultant(_kdef_y, _fxb, 2);
                _d   := Max([0] cat [Exponents(_m)[1] : _m in Monomials(_res)]);
                poly := Polynomial(Rationals(), [MonomialCoefficient(_res, _xv^_i) : _i in [0.._d]]);
            end if;
            poly := poly div GCD(poly, Derivative(poly));

            // Scan for non-linear non-univariate GB elements.
            // Resultant against the univariate yields extra univariates in higher-priority
            // variables; these feed extra_seen so SplitAutGrp extends K enough for BackSubAll.
            for g in GB do
                lv_g := Min([i : i in [1..7] | Exponents(LeadingMonomial(g))[i] ne 0]);
                if lv_g eq uni_var then continue; end if;
                deg_g_lv := Max([Exponents(m)[lv_g] : m in Monomials(g)]);
                if deg_g_lv le 1 then continue; end if;
                res := Resultant(g, uni, R7.uni_var);
                if IsZero(res) then continue; end if;
                vars_res := {};
                for m in Monomials(res) do
                    ev := Exponents(m);
                    for i in [1..7] do if ev[i] ne 0 then Include(~vars_res, i); end if; end for;
                end for;
                if not (#vars_res eq 1 and lv_g in vars_res) then continue; end if;
                deg_res := Max([Exponents(m)[lv_g] : m in Monomials(res)]);
                cf_res  := [MonomialCoefficient(res, R7.lv_g^d) : d in [0..deg_res]];
                if Type(k) eq FldRat then
                    ep := Polynomial(RationalField(), [RationalField()!c : c in cf_res]);
                else
                    _ek  := Polynomial(k, [k!c : c in cf_res]);
                    _exb := &+[(&+[(_Qxb!(Rationals()!Eltseq(Coefficient(_ek,_i))[_j]))*_yv^(_j-1)
                                   : _j in [1.._dk]]) * _xv^_i : _i in [0..Degree(_ek)]];
                    _er  := Resultant(_kdef_y, _exb, 2);
                    _ed  := Max([0] cat [Exponents(_m)[1] : _m in Monomials(_er)]);
                    ep   := Polynomial(Rationals(), [MonomialCoefficient(_er, _xv^_i) : _i in [0.._ed]]);
                end if;
                ep := ep div GCD(ep, Derivative(ep));
                for ep_fac in Factorization(ep) do
                    ep_f := ep_fac[1];
                    if Degree(ep_f) ge 2 and not exists{p : p in extra_seen | p eq ep_f} then
                        Append(~extra_seen, ep_f);
                    end if;
                end for;
            end for;

            cd_idx := #comp_data + 1;
            rat_roots_comp := [RationalField() | ];
            for fac in Factorization(poly) do
                f := fac[1];
                if Degree(f) eq 1 then
                    Append(~rat_roots_comp, -Coefficient(f, 0) / Coefficient(f, 1));
                elif not exists{p : p in seen_polys | p eq f} then
                    Append(~seen_polys, f);
                    Append(~comp_for_poly, cd_idx);
                end if;
            end for;
            Append(~comp_data, <poly, GB, uni_var, rat_roots_comp>);
        end for;

        univariates := seen_polys;

        if Verbose then
            printf "Step 2: %o base univariate(s), %o extra univariate(s) for K.\n",
                   #univariates, #extra_seen;
        end if;

        // Option A: est_deg from base univariates (extra_seen inflates it spuriously).
        // Only gate Variety on splitting-field size for k = Q; for k != Q Variety is always default.
        est_deg := #univariates gt 0 select LCM([Degree(f) : f in univariates]) else 1;
        if Type(k) eq FldRat then
            use_points := use_points and (est_deg lt 5);
        end if;
        if Verbose then
            printf "Option A: estimated splitting field degree = %o%o.\n", est_deg,
                use_points select " → Variety path" else "";
        end if;
    end if;

    // ------------------------------------------------------------------
    // Step 3: SplitAutGrp → splitting field K, automorphism group, root lists.
    // Fast path: one squarefree univariate from the lex GB.
    // Full path: all per-component univariates plus extra_seen.
    // ------------------------------------------------------------------
    if Verbose then printf "Step 3: Calling SplitAutGrp...\n"; end if;

    if gb_path_taken then
        // Separate irr factors of poly_fast (for s_{uvar_fast} iteration) from
        // fast_extra (for extending K).  root_ll_fast = all roots of poly_fast in K.
        irr_facs_poly       := [];
        rat_roots_poly_fast := [];
        for fac in Factorization(poly_fast) do
            f := fac[1];
            if Degree(f) eq 1 then
                Append(~rat_roots_poly_fast, -Coefficient(f, 0) / Coefficient(f, 1));
            elif Degree(f) ge 2 then
                Append(~irr_facs_poly, f);
            end if;
        end for;
        fast_polys := irr_facs_poly;
        for ep in fast_extra do
            if not exists{p : p in fast_polys | p eq ep} then Append(~fast_polys, ep); end if;
        end for;
        if #fast_polys eq 0 then
            K            := RationalField();
            Aut          := SymmetricGroup(1);
            aut_map      := false;
            root_ll_fast := [K!r : r in rat_roots_poly_fast];
        else
            K, Aut, aut_map, root_ll_all := SplitAutGrp(fast_polys);
            irr_roots    := &cat[root_ll_all[i] : i in [1..#irr_facs_poly]];
            root_ll_fast := [K!r : r in rat_roots_poly_fast] cat irr_roots;
        end if;
        root_ll := [];   // not used by GB path (Variety or BackSubAll-from-GB)
    else
        // SplitAutGrp requires the product of its inputs to be squarefree.
        // Norm polynomials from different PD components can share a factor even after
        // individual squarefree reduction (they're equal as Q-polys but got deduplicated
        // only by identity, not by common divisor).  Squarefree the combined list here.
        _sp_list := univariates cat extra_seen;
        if #_sp_list gt 0 then
            _sp_prod := &*_sp_list;
            if not IsSquarefree(_sp_prod) then
                _sp_sf   := _sp_prod div GCD(_sp_prod, Derivative(_sp_prod));
                _sp_list := [fac[1] : fac in Factorization(_sp_sf) | Degree(fac[1]) ge 2];
            end if;
        end if;
        if #_sp_list eq 0 then
            K := RationalField(); Aut := SymmetricGroup(1); aut_map := false;
            root_ll := [];
        else
            K, Aut, aut_map, root_ll_all := SplitAutGrp(_sp_list);
            // For k = Q (BackSubAll path): root_ll indexed by univariates; _sp_list equals
            // univariates cat extra_seen (squarefree was already guaranteed for k = Q by
            // the equality dedup), so root_ll_all[1..#univariates] is correct.
            // For k != Q (Variety path): root_ll is unused; set to [].
            root_ll := (use_points or Type(k) ne FldRat)
                       select []
                       else root_ll_all[1..#univariates];
        end if;
    end if;

    if Verbose then printf "Step 3: K = %o, |Aut| = %o.\n", K, #Aut; end if;

    // ------------------------------------------------------------------
    // Steps 4-5: Recover sections.  Three paths (checked in order):
    //   use_points = true       → Variety(I_K) over the splitting field K.
    //                              For k = Q: K came from SplitAutGrp (est_deg < 5).
    //                              For k != Q: K is the splitting field; Variety is
    //                              default (UsePD overrides to BackSubAll).
    //   gb_path_taken = true    → BackSubAll on GB_fast.  Default path for k = Q.
    //   else (UsePD=true path)  → BackSubAll per primary component from comp_data.
    // ------------------------------------------------------------------
    FK := FunctionField(K);
    tK := FK.1;

    // For k != Q, build an explicit embedding k -> K so generators of I (over k)
    // can be lifted to I_K (over K).  Both k and K are absolute number fields over Q;
    // find the image of k.1 in K by rooting DefiningPolynomial(k) in K.
    embed_k_K := false;
    if Type(k) ne FldRat and Type(K) ne FldRat then
        kpol_K  := ChangeRing(DefiningPolynomial(k), PolynomialRing(K));
        kgen_in_K := Roots(kpol_K, K)[1][1];
        embed_k_K := func<c | &+[K!Eltseq(c)[i] * kgen_in_K^(i-1) : i in [1..#Eltseq(c)]]>;
    end if;

    // BackSubAll: given a partial assignment sv_init (with sv_init[uvi] = root),
    // process non-univariate GB elements in descending priority order.
    // Linear elements yield one branch; non-linear elements (degree > 1 in their
    // leading variable) find ALL roots in K via Roots() and branch accordingly.
    // Returns a sequence of complete sv tuples.
    function BackSubAll(sv_init, non_uni, K)
        KT<T_bs> := PolynomialRing(K);
        svs := [sv_init];
        for pair in non_uni do
            lv      := pair[1];
            g       := pair[2];
            mons    := Monomials(g);
            new_svs := [];
            for sv in svs do
                // Build univariate h(T) in s_lv by substituting sv[lv+1..7]
                h := KT!0;
                for m in mons do
                    ev    := Exponents(m);
                    c     := K!MonomialCoefficient(g, m);
                    other := K!1;
                    for j in [lv+1..7] do
                        if ev[j] ne 0 then other *:= sv[j]^ev[j]; end if;
                    end for;
                    h +:= c * other * T_bs^ev[lv];
                end for;
                if IsZero(h) then Append(~new_svs, sv); continue; end if;
                d := Degree(h);
                if d le 1 then
                    c1 := Coefficient(h, 1);
                    c0 := Coefficient(h, 0);
                    if not IsWeaklyZero(c1) then
                        sv_new     := sv;
                        sv_new[lv] := -c0 / c1;
                        Append(~new_svs, sv_new);
                    else
                        Append(~new_svs, sv);
                    end if;
                else
                    // Non-linear: branch on every root in K
                    for rt in Roots(h, K) do
                        sv_new     := sv;
                        sv_new[lv] := rt[1];
                        Append(~new_svs, sv_new);
                    end for;
                end if;
            end for;
            svs := new_svs;
        end for;
        return svs;
    end function;

    Sections := [];

    if use_points then
        // Variety(I_K) finds all K-rational sections directly.
        // Coefficients of I lie in k; embed_k_K lifts them to K when k != Q.
        if Verbose then printf "Steps 4-5: Solving section ideal over K via Variety.\n"; end if;
        R7K<s1K,s2K,s3K,s4K,s5K,s6K,s7K> := PolynomialRing(K, 7, "lex");
        gens_K := [];
        for g in Generators(I) do
            gK := R7K!0;
            for mon in Monomials(g) do
                ev := Exponents(mon);
                c  := MonomialCoefficient(g, mon);
                cK := embed_k_K cmpne false select embed_k_K(c) else K!c;
                gK +:= cK * &*[R7K.j^ev[j] : j in [1..7]];
            end for;
            Append(~gens_K, gK);
        end for;
        I_K := ideal<R7K | gens_K>;
        for pt in Variety(I_K) do
            xt := pt[1]*tK^2 + pt[2]*tK + pt[3];
            yt := pt[4]*tK^3 + pt[5]*tK^2 + pt[6]*tK + pt[7];
            Append(~Sections, [xt, yt]);
        end for;
    elif gb_path_taken then
        // BackSubAll-from-GB: iterate roots of poly_fast through the lex GB directly.
        // Avoids primary decomposition entirely; works for any est_deg.
        if Verbose then printf "Steps 4-5: Building sections via BackSubAll on lex GB.\n"; end if;
        non_uni_fast := [];
        for g in GB_fast do
            lv := Min([j : j in [1..7] | Exponents(LeadingMonomial(g))[j] ne 0]);
            if lv ne uvar_fast then Append(~non_uni_fast, <lv, g>); end if;
        end for;
        Sort(~non_uni_fast, func<a, b | b[1] - a[1]>);
        for root in root_ll_fast do
            sv_init            := [K!0 : j in [1..7]];
            sv_init[uvar_fast] := root;
            for sv in BackSubAll(sv_init, non_uni_fast, K) do
                xt := sv[1]*tK^2 + sv[2]*tK + sv[3];
                yt := sv[4]*tK^3 + sv[5]*tK^2 + sv[6]*tK + sv[7];
                Append(~Sections, [xt, yt]);
            end for;
        end for;

    else
        if Verbose then printf "Steps 4-5: Building sections from roots...\n"; end if;

        for i in [1..#univariates] do
            cd   := comp_data[comp_for_poly[i]];
            GB_i := cd[2];
            uvi  := cd[3];
            // Sort non-univariate elements once per component (descending priority)
            non_uni := [];
            for g in GB_i do
                lv := Min([j : j in [1..7] | Exponents(LeadingMonomial(g))[j] ne 0]);
                if lv ne uvi then Append(~non_uni, <lv, g>); end if;
            end for;
            Sort(~non_uni, func<a, b | b[1] - a[1]>);
            for root in root_ll[i] do
                sv_init      := [K!0 : j in [1..7]];
                sv_init[uvi] := root;
                for sv in BackSubAll(sv_init, non_uni, K) do
                    xt := sv[1]*tK^2 + sv[2]*tK + sv[3];
                    yt := sv[4]*tK^3 + sv[5]*tK^2 + sv[6]*tK + sv[7];
                    Append(~Sections, [xt, yt]);
                end for;
            end for;
        end for;

        // Process rational roots stored in comp_data (from linear factors of base polys).
        // These were excluded from seen_polys so SplitAutGrp never saw a linear input,
        // but the corresponding sections are still valid and must be recovered.
        for cd_r in comp_data do
            rat_roots_r := cd_r[4];
            if #rat_roots_r eq 0 then continue; end if;
            GB_r  := cd_r[2];
            uvi_r := cd_r[3];
            non_uni_r := [];
            for g in GB_r do
                lv := Min([j : j in [1..7] | Exponents(LeadingMonomial(g))[j] ne 0]);
                if lv ne uvi_r then Append(~non_uni_r, <lv, g>); end if;
            end for;
            Sort(~non_uni_r, func<a, b | b[1] - a[1]>);
            for root in rat_roots_r do
                sv_init        := [K!0 : j in [1..7]];
                sv_init[uvi_r] := K!root;
                for sv in BackSubAll(sv_init, non_uni_r, K) do
                    xt := sv[1]*tK^2 + sv[2]*tK + sv[3];
                    yt := sv[4]*tK^3 + sv[5]*tK^2 + sv[6]*tK + sv[7];
                    Append(~Sections, [xt, yt]);
                end for;
            end for;
        end for;

    end if;  // use_points / gb_path_taken

    if Verbose then printf "Steps 4-5: %o total section(s) found.\n", #Sections; end if;

    // ------------------------------------------------------------------
    // Step 5b: Torsion and independent generators via reduction mod p
    // ------------------------------------------------------------------
    if Verbose then printf "Step 5b: Finding torsion and generators...\n"; end if;

    // Precompute defining polynomial as Z[x] for fast completely-split checks mod p.
    // Avoids Integers(K) (maximal order), which is a severe bottleneck for deg(K) > 100.
    // A prime p splits completely in K iff DefiningPolynomial(K) factors into distinct
    // linear factors mod p — verified by polynomial factorization over GF(p).
    if Type(K) ne FldRat then
        Kpol_Z := PolynomialRing(Integers())!DefiningPolynomial(K);
    end if;

    // Select a good prime < 2^20 satisfying:
    //   (a) discriminant does not vanish mod p
    //   (b) no Weierstrass coefficient has a pole mod p
    //   (c) p splits completely in K so ResidueClassField = GF(p), not GF(p^f)
    // Good-prime discriminant check coefficients (disc_E is in k[t] for all k).
    // For k = Q: c in Q, check Numerator(c) mod p.
    // For k != Q: c in k, check via Valuation(Norm(c), p).
    disc_cf := Coefficients(disc_E);
    good_prime := 0;
    while good_prime eq 0 do
        p_cand := RandomPrime(20);
        if Type(k) eq FldRat then
            // k = Q: c mod p = 0 iff p | Numerator(c) (denominator coprime to good p).
            if forall{c : c in disc_cf | Integers()!Numerator(c) mod p_cand eq 0}
            then continue; end if;
            ok := true;
            for a in ai do
                _den_cf := Coefficients(Denominator(a));
                if forall{c : c in _den_cf |
                    Integers()!Numerator(c) mod p_cand eq 0}
                then ok := false; break; end if;
            end for;
        else
            // k != Q: a coefficient c in k vanishes mod p (under every embedding) iff
            // p | Norm_{k/Q}(c).  Use Valuation(Norm(c), p) > 0 as the check.
            if forall{c : c in disc_cf | IsZero(c) or Valuation(Norm(c), p_cand) gt 0}
            then continue; end if;
            ok := true;
            for a in ai do
                _den_cf := Coefficients(Denominator(a));
                if forall{c : c in _den_cf |
                    IsZero(c) or Valuation(Norm(c), p_cand) gt 0}
                then ok := false; break; end if;
            end for;
        end if;
        // Completely-split check: DefiningPolynomial factors into distinct linear factors mod p.
        // This is purely polynomial arithmetic over GF(p) — no maximal order needed.
        if ok and Type(K) ne FldRat then
            Kpol_cand := ChangeRing(Kpol_Z, GF(p_cand));
            facs_cand := Factorization(Kpol_cand);
            if not forall{fac : fac in facs_cand | Degree(fac[1]) eq 1} then
                ok := false;
            end if;
        end if;
        if ok then
            good_prime := p_cand;
            if Type(K) ne FldRat then facs_K_modp := facs_cand; end if;
        end if;
    end while;

    if Verbose then printf "Step 5b: Reducing mod p = %o.\n", good_prime; end if;

    // Build residue map K -> GF(p).
    // facs_K_modp was saved from the completely-split check — no Decomposition needed.
    // Evaluate the coordinate polynomial of c at the mod-p root using compiled Horner.
    if Type(K) eq FldRat then
        Fq    := GF(good_prime);
        red_K := func<c | Fq!Numerator(c) * (Fq!Denominator(c))^(-1)>;
    else
        Fq     := GF(good_prime);
        a_root := -Coefficient(facs_K_modp[1][1], 0);
        function red_K_fn(c)
            coords := Eltseq(c);
            return Evaluate(Polynomial(Fq,
                [Fq!Numerator(r) * (Fq!Denominator(r))^(-1) : r in coords]), a_root);
        end function;
        red_K := red_K_fn;
    end if;

    // k -> GF(p)
    if Type(k) eq FldRat then
        red_k := func<c | Fq!Numerator(c) * (Fq!Denominator(c))^(-1)>;
    elif embed_k_K cmpne false then
        red_k := func<c | red_K(embed_k_K(c))>;
    else
        // K = Q (rank-0 case or all-rational sections); k elements are rational
        red_k := func<c | Fq!Numerator(Rationals()!c) * (Fq!Denominator(Rationals()!c))^(-1)>;
    end if;

    FFq := FunctionField(Fq);
    tq  := FFq.1;

    function ReduceToFFq(f, red_fn)
        // Same scalar-dispatch as _ff_to_Rk: ISA + Type(k) branch for num and den.
        if IsZero(f) then return FFq!0; end if;
        num := Numerator(f);
        den := Denominator(f);
        cf_n := ISA(Type(num), RngUPolElt) select Coefficients(num) else [k!num];
        cf_d := ISA(Type(den), RngUPolElt) select Coefficients(den) else [k!den];
        num_q := #cf_n eq 0 select FFq!0
                            else &+[red_fn(cf_n[i]) * tq^(i-1) : i in [1..#cf_n]];
        den_q := #cf_d eq 0 select FFq!1
                            else &+[red_fn(cf_d[i]) * tq^(i-1) : i in [1..#cf_d]];
        return num_q / den_q;
    end function;

    // Reduce E mod p -> Ered over GF(p)(t)
    ai_q := [ReduceToFFq(a, red_k) : a in ai];
    Ered := EllipticCurve(ai_q);

    // Reduce every section to a point on Ered.
    // Bug 1+2 fix: sections are K[t]-polynomials; use indexed access and apply
    // red_K directly to each K-coefficient rather than routing through ReduceToFFq.
    pts_red := [];
    for i in [1..#Sections] do
        cf_x := Coefficients(Numerator(Sections[i][1]));
        cf_y := Coefficients(Numerator(Sections[i][2]));
        x_red := #cf_x eq 0 select FFq!0 else &+[red_K(cf_x[j]) * tq^(j-1) : j in [1..#cf_x]];
        y_red := #cf_y eq 0 select FFq!0 else &+[red_K(cf_y[j]) * tq^(j-1) : j in [1..#cf_y]];
        Append(~pts_red, Ered![x_red, y_red]);
    end for;

    // Torsion detection and independent generators both use pts_red on Ered.
    // Working over GF(p)(t) is fast; working over K(t) for large K is intractable.
    TorsPts  := [];
    TorsIdxs := {};
    for i in [1..#Sections] do
        if HeightPairing(pts_red[i], pts_red[i]) eq 0 then
            Append(~TorsPts, Sections[i]);
            Include(~TorsIdxs, i);
        end if;
    end for;

    NonTorsIdxs := [i : i in [1..#Sections] | i notin TorsIdxs];

    GenSections := [];
    GenPtsRed   := [];
    if #NonTorsIdxs gt 0 then
        NonTorsPtsRed := [pts_red[i] : i in NonTorsIdxs];
        IndPts := IndependentGenerators(NonTorsPtsRed);
        for pt in IndPts do
            idx := Index(NonTorsPtsRed, pt);
            if idx gt 0 then
                Append(~GenSections, Sections[NonTorsIdxs[idx]]);
                Append(~GenPtsRed,   NonTorsPtsRed[idx]);
            end if;
        end for;
    end if;

    r := #GenSections;
    if Verbose then
        printf "Step 5b: %o torsion point(s), rank = %o.\n", #TorsPts, r;
    end if;

    // ------------------------------------------------------------------
    // Step 6: Galois representation via GModule
    // ------------------------------------------------------------------
    if Verbose then printf "Step 6: Building Galois representation...\n"; end if;

    IrrReps := [];
    Chars    := [];

    // Determine the acting Galois group:
    //   k = Q  → Gal(K/Q) = Aut (generators already fix k trivially)
    //   k != Q → Gal(K/k) = stabiliser of kgen_in_K inside Aut = Gal(K/Q).
    //             Elements of Aut not fixing k map E to sigma(E) != E, so they
    //             do not act on MW(E/k(t)).
    GalKk := Aut;  // default: k = Q, Gal(K/k) = Gal(K/Q)
    if r gt 0 and Type(k) ne FldRat and embed_k_K cmpne false then
        GalKk := sub<Aut |
            [sigma : sigma in Aut | aut_map(sigma)(kgen_in_K) eq kgen_in_K]>;
        if Verbose then
            printf "Step 6: |Gal(K/Q)| = %o, |Gal(K/k)| = %o (index = [k:Q] = %o).\n",
                #Aut, #GalKk, #Aut div #GalKk;
        end if;
    end if;

    if r gt 0 then
        // For each generator σ of Gal(K/k), build the r×r integer matrix M_σ whose
        // (i,j) entry is the coefficient of g_j in σ(g_i) = Σ_j a_{ij} * g_j.
        // Method: reduce σ(g_i) to Ered, then solve via the Neron-Tate Gram matrix.
        //   v[j] = <σ(g_i), g_j>;  since v = a * GramMat,  a = v * GramMat^{-1}.
        // HeightPairing over GF(p)(t) is exact (rational) and fast.
        GramMat := Matrix(Rationals(), r, r,
            [HeightPairing(GenPtsRed[i], GenPtsRed[j]) : i in [1..r], j in [1..r]]);
        GramInv := GramMat^(-1);

        aut_mats := [];
        for sigma in Generators(GalKk) do
            phi_sigma := aut_map(sigma);
            rows := [];
            for i in [1..r] do
                s    := GenSections[i];
                cf_x := Coefficients(Numerator(s[1]));
                cf_y := Coefficients(Numerator(s[2]));
                x_sig := #cf_x eq 0 select FFq!0
                         else &+[red_K(phi_sigma(cf_x[j])) * tq^(j-1) : j in [1..#cf_x]];
                y_sig := #cf_y eq 0 select FFq!0
                         else &+[red_K(phi_sigma(cf_y[j])) * tq^(j-1) : j in [1..#cf_y]];
                P_sig := Ered![x_sig, y_sig];
                v := Vector(Rationals(), [HeightPairing(P_sig, GenPtsRed[j]) : j in [1..r]]);
                a := v * GramInv;
                Append(~rows, [Round(a[j]) : j in [1..r]]);
            end for;
            Append(~aut_mats, Matrix(Integers(), rows));
        end for;

        if #aut_mats gt 0 then
            GP := MatrixGroup<r, Rationals() | [ChangeRing(m, Rationals()) : m in aut_mats]>;
            M  := GModule(GP);
            IC := ConstituentsWithMultiplicities(M);
            IrrReps := IC;
            CT := RationalCharacterTable(GP);
            Chars := [CT[i] : i in [1..#CT]
                             | exists{pair : pair in IC | Character(pair[1]) eq CT[i]}];
        end if;
    end if;

    if Verbose then
        printf "Step 6: %o irreducible constituent(s).\n", #IrrReps;
    end if;

    return r, K, Aut, GenSections, TorsPts, IrrReps, Chars;
end function;
