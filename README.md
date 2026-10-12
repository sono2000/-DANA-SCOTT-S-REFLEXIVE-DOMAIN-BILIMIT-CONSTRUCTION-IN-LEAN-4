# Operational Arithmetic, Krein Space Spectral Theory, and the Profinite Horizon
### *Constructive Foundations from Dana Scott's $D_\infty$ to the Riemann Hypothesis in Lean 4*

**Author:** Thomas William Norman  
**Date:** 12th October 2026  
**Lean Version:** `v4.35.0-rc4` (with latest Mathlib)  
**Verification Status:** Zero `sorry` | Audited via `#print axioms`  
**License:** Apache License 2.0  

---

## Overview

Can the discrete laws of arithmetic and the spectral properties of prime numbers emerge directly from the continuous foundations of computer science? 

This repository contains a complete, end-to-end formalization in **Lean 4** (~11,000 lines across 18 modules) investigating this question inside Dana Scott's reflexive domain bilimit $D_\infty \cong [D_\infty \to_\omega D_\infty]$. 

* **Part I (Modules 1–15):** Proves that Church numerals inside $D_\infty$ form an internal Natural Numbers Object whose information order collapses to a discrete antichain ($x \sqsubseteq y \iff x = y$). While finite domain projections naturally act as a prime sieve across discrete lattice heights ($H_1=2, H_2=6, H_3=60$) before collapsing to parity under Dilworth's theorem, we bypass finite state-space explosion by constructing closed cyclic step combinators—lifting arithmetic unconditionally to the profinite integers $\widehat{\mathbb{Z}}$.
* **Part II (Modules 16–18):** Synthesizes arithmetic ratio matrices ($R_{i,j} = \operatorname{lcm}(i,j)/\operatorname{gcd}(i,j)$) in pure $\lambda$-calculus, proves sub-logarithmic factorial reconstruction ($K=13$ for $n=100{,}000$), establishes positive-definiteness of the reciprocal LCM matrix via Euler totients ($A = B B^T \succ 0$), locks Krein eigenvalues to the real line ($\operatorname{Im}(\lambda) = 0$), bounds infinite column energy by $8/9$, and proves a machine-checked equivalence between the operator's sublinear trace growth and the **Riemann Hypothesis**.

---

## The Master Scorecard: Five Quantified Pillars

| # | Pillar | Classical / Finite Barrier | Resolution in $D_\infty$ | Quantified Benchmark | Key Lean 4 Theorem |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1** | **The Cyclic Gear Trick** | State explosion ($H_4 = 7.23 \times 10^6$) crashes into $\bot$. | Internal $m$-ary Church selectors (`step_m_comb`) along 1D cyclic orbits. | Slashes state space to strictly **$m$ states**; evaluates **100% of $\mathbb{N}$**. | `step_m_cyclic` (Mod 15) |
| **2** | **Hidden Emptiness** | Ratio matrix $R_{i,j} = \operatorname{lcm}/\operatorname{gcd}$ is dense with massive integers. | Möbius divisor inversion yielding an exact analytic formula for $R_n^{-1}$. | **73.3% zero** at $n=30$; **100% asymptotically sparse**; $\det(R_n) \neq 0$. | `dyadic_decomposition_exact` (Mod 16) |
| **3** | **Sub-Log Telescoping** | Infinite profinite trees suffer modular wrap-around error. | Non-wrapping factorial projection whenever $n^2 < (K+1)!$. | Exact $100\text{k} \times 100\text{k}$ table ($10^{10}$ entries) at **depth $K=13$**. | `reconstruction_theorem_from_A1` (Mod 16) |
| **4** | **Krein Energy Anchor** | Indefinite Krein metrics suffer complex eigenvalue collisions. | Totient Gramian factorization ($A \succ 0$) and Norman similarity lock. | Column $\ell^2$-energy **$\le 8/9$**; $\operatorname{Im}(\lambda) = 0.00$; ground gap **$>14:1$**. | `self_adjoint_real_eigenvalue_lock` (Mod 17) |
| **5** | **Axiomatic Firewall** | Unverified assumptions in spectral attacks on RH. | Constructive square-full splitting ($d = a^2 b^3$); deletion of Axioms C6 & B5d. | **0 custom axioms** in kernel signature; conditional reduction $\sum p \iff \text{RH}$. | `trace_sum_rh_equivalence_under_all_hypotheses` (Mod 18) |

---

## Quick Verification (Zero Setup in Your Browser)

You do not need to install any local toolchains or configure build files to verify this proof. The entire codebase is designed to run directly in the **Lean 4 Web Editor**:

1. Open the raw `.lean` file in this repository and **Copy** the code.
2. Go to **[https://live.lean-lang.org](https://live.lean-lang.org)** (running **Latest Mathlib with Lean v4.35.0-rc4**).
3. **Paste** the code into the left editor pane.
4. Wait for the status bar to finish checking, then inspect the **Lean Infoview** on the right pane under **All Messages** to view the `#print axioms` audit for all 210+ verified declarations.

---

## Architecture & Module Guide

The formalization is organized sequentially across 18 modules inside the main Lean file:

* **Modules 1–5 (Lines 1–1386): Reflexive Domain Foundations**
  * Pointed $\omega$-CPOs, chain supremum interchange, Embedding-Projection (EP) pairs, projective towers, and the master isomorphism $D_\infty \cong [D_\infty \to_\omega D_\infty]$ (`scott_reflexive_domain_full_isomorphism`, `D_infty_nontrivial`).
* **Modules 6–8 (Lines 1387–2736): Combinatory Logic & Peano Arithmetic**
  * Internal combinators ($\mathbf{I}, \mathbf{K}, \mathbf{S}, \mathbf{Y}$), de Bruijn $\beta\eta$-soundness (`denotational_soundness`), ground-state annihilation of looping terms (`omega_eval_bot`), Peano injectivity (`church_injective`), and the Master Antichain Theorem (`church_le_injective`).
* **Module 9 & 9B (Lines 2737–3259): Operational Primality & The Internal NNO**
  * Constructive primality witnesses (`two_is_prime`, `three_is_prime`, `five_is_prime`, `four_not_prime`, `six_not_prime`), the universal primitive recursor $D_{\mathrm{nat\_rec}}$ (`D_nat_rec_unique`), and the Discrete Order Collapse (`internal_nat_le_iff_eq`).
* **Modules 10–12 (Lines 3260–4464): The Finite-Stage Scott Sieve & Fixpoint Collapse**
  * Lattice height recurrence ($H_0=1, H_1=2, H_2=6, H_3=60$), initial prime resolution at Stage 3 (`stage_3_separation`), Dilworth poset width parity collapse, and the successor fixed point identity $\omega_{\mathrm{fix}} = \mathbf{K} \cdot \mathbf{Y}$ (`omega_fix_eq_limit`).
* **Module 13 (Lines 4465–5608): The Profinite Horizon $\widehat{\mathbb{Z}}$**
  * Coherent residue threads over positive moduli, universal inverse limit property (`inverse_limit_lift_unique`), `CommRing` instance, factorial cofinality (`modulus_eventually_dvd`), complete prefix ultrametric space (`dProf_ultrametric`, `prof_cauchy_complete`), metric-cylinder identification (`metric_ball_eq_cylinder`), and the Master Four-Way Equivalence (`church_four_way_equivalence`).
* **Modules 14–15 (Lines 5609–6727): The Cyclic Gear Trick & Unconditional Factorization**
  * Ternary and general $m$-ary Church selectors (`S0_spec`, `selector_comb_spec`), cyclic step combinators (`step3_S0`, `step_m_cyclic`), continuous Modulo-3 and Modulo-6 observers (`scott_mod3_obs_church`, `scott_mod6_obs_church`), general Scott continuity (`default_observe_cSup`), and unconditional Church-profinite factorization (`default_church_profinite_factorization`).
* **Module 16 (Lines 6728–7756): Operational Ratio Matrices & Sylvester Inertia**
  * Pure $\lambda$-calculus synthesis of $M_{\mathrm{op}}$ (`M_op_church_eval`), sub-logarithmic factorial reconstruction (`reconstruction_theorem_from_A1`), exact dyadic decomposition (`dyadic_decomposition_exact`), and Sylvester inertia parity lock (`concrete_J_trace_eq_inertia_difference`).
* **Module 17 (Lines 7757–9263): Reciprocal LCM Positivity & Krein Space Definitizability**
  * Strict positive-definiteness of $A_{i,j} = 1/\operatorname{lcm}(i,j)$ via Euler totient Gramians (`B3_finite_reciprocal_lcm_strictly_pos_def`), similarity conjugation (`concrete_similarity_conjugation`), the Norman Real Eigenvalue Lock (`self_adjoint_real_eigenvalue_lock`), telescoping bound $|g| \le 2$ (`abs_gArith_real_le_two`), universal $8/9$ column energy bound (`A_canon_fin_energy_le`), and Genus-4 Weierstrass spectral bridge (`canonical_weierstrass_product_entire`).
* **Module 18 (Lines 9264–10916): Square-Full Convolutions & The Axiomatic Firewall**
  * Epistemic Blindness No-Go Theorem (`epistemic_blindness_of_krein_symmetry`), square-full support of the Dirichlet inverse $b = p * 1$ (`b_coeff_eq_zero_of_not_square_full`, `b_coeff_prime_pow_eq`), Dirichlet hyperbola convolution identity (`AxiomaticRegistry.B5b_trace_sum_eq_dirichlet_convolution`), the Mertens Transfer Theorem (`mertens_transfer_power_bound_global`), and the machine-verified equivalence to the Riemann Hypothesis (`trace_sum_rh_equivalence_under_all_hypotheses`).

---

## The Axiomatic Firewall (`#print axioms` Audit)

We enforce strict epistemic demarcation across the codebase:

1. **Zero Custom Axioms in Modules 1–16, Module 17 (Positivity & Energy Bounds), and Module 18:**
   All algebraic, domain-theoretic, matrix positivity, and RH equivalence theorems depend exclusively on Lean's standard foundational kernel:
   ```text
   'scott_reflexive_domain_full_isomorphism' depends on axioms: [propext, choice, Quot.sound]
   'church_four_way_equivalence' depends on axioms: [propext, choice, Quot.sound]
   'default_church_profinite_factorization' depends on axioms: [propext, choice, Quot.sound]
   'dyadic_decomposition_exact' depends on axioms: [propext, choice, Quot.sound]
   'B3_finite_reciprocal_lcm_strictly_pos_def' depends on axioms: [propext, choice, Quot.sound]
   'self_adjoint_real_eigenvalue_lock' depends on axioms: [propext, choice, Quot.sound]
   'A_canon_fin_energy_le' depends on axioms: [propext, choice, Quot.sound]
   'mertens_transfer_power_bound_global' depends on axioms: [propext, choice, Quot.sound]
   'trace_sum_rh_equivalence_under_all_hypotheses' depends on axioms: [propext, choice, Quot.sound]
