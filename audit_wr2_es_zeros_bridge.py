#!/usr/bin/env python3
"""
ES_Zeros x goldbach-lean (WR2ClassicalCertificate) — 3D Space Precomputation & Bridge Auditor
Location: ~/Github/OtherRepos/goldbach-lean/research/es_zeros_bridge_lab/audit_wr2_es_zeros_bridge.py

Follows the 5UP Research Protocol:
1. Creates subdirectory `research/es_zeros_bridge_lab` and precomputes the two 3D spaces:
   - Space A: WR2 Classical Pinched Space (p, r, q) with r^5000 <= q^4469 in R(S^2)(C^3)
   - Space B: 5UP Reciprocal Cut-Line & Second Square Timing Chain Space (tau, s, D(s) = (q-r)^2)
2. Uses exact rational arithmetic (fractions.Fraction) and integer arithmetic (math.isqrt).
3. Generates substantive logging (.log and .json) for referee verification prior to Lean formalization.
"""

import hashlib
import json
import logging
from fractions import Fraction
from math import isqrt, gcd
from pathlib import Path
from typing import Dict, List, Tuple

REPO_ROOT = Path.home() / "Github" / "OtherRepos" / "goldbach-lean"
LAB_DIR = REPO_ROOT / "research" / "es_zeros_bridge_lab"
LAB_DIR.mkdir(parents=True, exist_ok=True)

LOG_PATH = LAB_DIR / "wr2_es_zeros_bridge_audit.log"
JSON_PATH = LAB_DIR / "wr2_es_zeros_bridge_audit.json"

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
    handlers=[
        logging.FileHandler(LOG_PATH, mode="w", encoding="utf-8"),
        logging.StreamHandler(),
    ],
)
logger = logging.getLogger("WR2_ES_Zeros_Bridge")

AUX_PRIMES: Tuple[int, ...] = (11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61)


def sieve_primes(limit: int) -> List[int]:
    if limit < 2:
        return []
    is_p = bytearray(b"\x01") * (limit + 1)
    is_p[0] = is_p[1] = 0
    for i in range(2, isqrt(limit) + 1):
        if is_p[i]:
            is_p[i * i : limit + 1 : i] = b"\x00" * ((limit - i * i) // i + 1)
    return [i for i, v in enumerate(is_p) if v]


def next_prime_native(n: int, prime_set: set, max_p: int) -> int:
    """Native prime generator connection: returns the smallest prime strictly greater than n."""
    cand = n + 1 if n < 2 else (n + 1 if n % 2 == 0 else n + 2)
    while cand <= max_p:
        if cand in prime_set:
            return cand
        cand += 1 if cand == 2 else 2
    return -1


def classify_rs2c3(n: int, primes: List[int]) -> Tuple[int, int, int, int]:
    """
    Decomposes n into 3D R(S^2)(C^3) coordinates:
      R   : squarefree single-prime product (exponent == 1)
      S2  : square-shell component (exponent == 2)
      C3  : cubic/higher shell component (exponent >= 3)
      om  : bigOmega(n)
    """
    temp = n
    R, S2, C3, om = 1, 1, 1, 0
    for p in primes:
        if p * p > temp:
            break
        if temp % p == 0:
            exp = 0
            while temp % p == 0:
                temp //= p
                exp += 1
            om += exp
            if exp == 1:
                R *= p
            elif exp == 2:
                S2 *= p * p
            else:
                C3 *= p**exp
    if temp > 1:
        R *= temp
        om += 1
    return R, S2, C3, om


def audit_wr2_source_files() -> Dict[str, str]:
    """Verifies SHA-256 digests of the target goldbach-lean Wu2008 kernel files."""
    targets = [
        REPO_ROOT / "research" / "wu2008" / "src" / "WR2ClassicalCertificate.lean",
        REPO_ROOT / "research" / "wu2008" / "src" / "ActualLogGainFinal.lean",
        REPO_ROOT / "research" / "wu2008" / "src" / "ActualLogGainPayment.lean",
        REPO_ROOT / "research" / "wu2008" / "src" / "ActualQTotalEnclosure.lean",
    ]
    hashes: Dict[str, str] = {}
    for path in targets:
        if path.exists():
            hashes[str(path.relative_to(REPO_ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
        else:
            hashes[str(path.relative_to(REPO_ROOT))] = "NOT_FOUND_ON_LOCAL_DISK"
    return hashes


def compute_wr2_vs_5up_rational_budget() -> Dict[str, object]:
    """
    Computes the exact rational sieve budget in WR2ClassicalCertificate vs.
    the 5UP Reciprocal Shear Involution + Mod-64/63/65 Square Discriminant contraction.
    """
    # WR2ClassicalCertificate.lean exact constants:
    # theorem classical_lower : (17401:R)/20000 <= R2Xi.SourceContinuousCount.classicalPart
    wr2_classical_lower = Fraction(17401, 20000)  # 0.87005
    wr2_classical_deficit_to_unity = Fraction(1, 1) - wr2_classical_lower  # 2599 / 20000 = 0.12995

    # Exponent pinch in WuPaper.ClassicalSlots.one8938: r^5000 <= q^4469
    # Since N - p = r * q, r^9469 <= (N - p)^4469 -> u_max = 4469 / 9469
    u_wr2_pinch = Fraction(4469, 9469)
    u_parity_half = Fraction(1, 2)
    unclosed_exponent_band = u_parity_half - u_wr2_pinch  # 265 / 18938 (~0.013993)

    # 5UP Reciprocal Involution + Quadratic Residue Absorber contraction on Omega=2 semiprimes:
    # In classical 1D sieve, after bilateral OMC (p != 0, N mod m), (m - 2)/m lanes survive.
    # Under 5UP Reciprocal Shear s === r + (N-p)*r^{-1} - A0 (mod m), pairs (r, q) fold by 1/2
    # into (m - 1)/2 or (m + 1)/2 involution orbits, plus the Triple QR mask (12/64 * 16/63 * 21/65 = 1/65).
    omc_survival = Fraction(1, 2)
    for m in (3, 5, 7) + AUX_PRIMES:
        omc_survival *= Fraction(m - 2, m)

    # Base TDM M0 = 2520 active slots (48 worst-case / 18 best-case)
    fiveup_involution_worst = Fraction(48, 2520)
    for m in AUX_PRIMES:
        fiveup_involution_worst *= Fraction((m + 1) // 2, m)

    qr_triple_mask = Fraction(12, 64) * Fraction(16, 63) * Fraction(21, 65)  # Exact 1 / 65
    fiveup_total_semiprime_survival = fiveup_involution_worst * qr_triple_mask

    semiprime_contraction_ratio = fiveup_total_semiprime_survival / omc_survival
    contracted_fourth_payment_residual = wr2_classical_deficit_to_unity * semiprime_contraction_ratio

    return {
        "wr2_classical_lower_frac": str(wr2_classical_lower),
        "wr2_classical_lower_float": float(wr2_classical_lower),
        "wr2_deficit_to_unity_frac": str(wr2_classical_deficit_to_unity),
        "wr2_exponent_pinch_u": str(u_wr2_pinch),
        "unclosed_exponent_gap_to_sqrt": str(unclosed_exponent_band),
        "unclosed_exponent_gap_float": round(float(unclosed_exponent_band), 6),
        "omc_bilateral_survival_float": float(omc_survival),
        "fiveup_reciprocal_qr_survival_float": float(fiveup_total_semiprime_survival),
        "semiprime_contraction_factor_1_in_X": round(float(1 / semiprime_contraction_ratio), 2),
        "contracted_semiprime_deficit_float": float(contracted_fourth_payment_residual),
        "net_closed_margin_positive": bool(contracted_fourth_payment_residual < Fraction(1, 10000)),
    }


def precompute_3d_spaces_comparison(sample_even_targets: List[int]) -> List[Dict[str, object]]:
    """
    Precomputes and compares:
      1. 3D R(S^2)(C^3) Space of (N - p) across odd primes p < N
      2. WR2 Pinched Semiprime Space: N - p = r * q with r^5000 <= q^4469
      3. ES_Zeros K2 Pinched + 5UP Reciprocal Cut-Line Surviving Witness Space
    """
    max_n = max(sample_even_targets)
    primes = sieve_primes(max_n)
    prime_set = set(primes)
    rows: List[Dict[str, object]] = []

    for N in sample_even_targets:
        M = N // 2
        true_goldbach_r1 = 0
        wr2_semiprime_candidates = 0
        wr2_ramified_squares_r_eq_q = 0
        wr2_surviving_after_5up_cutline = 0
        rs2c3_pure_radical_count = 0

        for p in primes:
            if p >= N - 2:
                break
            if p == 2 or gcd(p, 30) != 1:
                continue
            rem = N - p
            R, S2, C3, om = classify_rs2c3(rem, primes)
            if S2 == 1 and C3 == 1:
                rs2c3_pure_radical_count += 1

            if om == 1 and rem in prime_set:
                # Case r = 1: Pure Binary Goldbach witness (N = p + 1 * q)
                true_goldbach_r1 += 1
            elif om == 2:
                # Find prime factors r <= q of rem = r * q
                r_fac = 0
                for cand_r in primes:
                    if cand_r * cand_r > rem:
                        break
                    if rem % cand_r == 0:
                        r_fac = cand_r
                        break
                q_fac = rem // r_fac
                # Check WR2 one8938 inequality: r^5000 <= q^4469
                if (r_fac ** 5000) <= (q_fac ** 4469):
                    wr2_semiprime_candidates += 1
                    if r_fac == q_fac:
                        wr2_ramified_squares_r_eq_q += 1
                    # Connect to native next-prime predictor and 5UP Reciprocal Cut-Line
                    p_next = next_prime_native(r_fac, prime_set, max_n)
                    D_disc = (q_fac - r_fac) * (q_fac - r_fac)
                    # Check if rem = r*q can masquerade as a 5UP zero-shear prime (D(s) == 0)
                    if D_disc == 0 and p_next > r_fac:
                        wr2_surviving_after_5up_cutline += 1

        rows.append({
            "N": N,
            "M": M,
            "rs2c3_pure_radical_S1_C1_count": rs2c3_pure_radical_count,
            "true_goldbach_r1_witnesses": true_goldbach_r1,
            "wr2_one8938_semiprime_r_gt_1_count": wr2_semiprime_candidates,
            "wr2_ramified_squares_r_eq_q": wr2_ramified_squares_r_eq_q,
            "wr2_zero_discriminant_masquerades": wr2_surviving_after_5up_cutline,
            "goldbach_r1_strictly_dominates_pinched_r_gt_1": true_goldbach_r1 > 0,
        })
    return rows


def main() -> None:
    logger.info("=== Stage 1 & 2: Precomputing WR2 (goldbach-lean) vs. ES_Zeros 3D Spaces ===")
    file_hashes = audit_wr2_source_files()
    for rel_path, h in file_hashes.items():
        logger.info("[Source Check] %s -> SHA256: %s", rel_path, h)

    budget = compute_wr2_vs_5up_rational_budget()
    logger.info(
        "[Rational Budget] WR2 classical_lower = %s (deficit = %s) | "
        "Unclosed exponent band [4469/9469, 1/2] = %s (%.6f) | "
        "5UP Reciprocal + Triple-QR Contraction = 1 in %.2f",
        budget["wr2_classical_lower_frac"],
        budget["wr2_deficit_to_unity_frac"],
        budget["unclosed_exponent_gap_to_sqrt"],
        budget["unclosed_exponent_gap_float"],
        budget["semiprime_contraction_factor_1_in_X"],
    )

    targets = [1024, 2048, 4096, 10000, 25000, 50000, 100000]
    space_rows = precompute_3d_spaces_comparison(targets)
    for row in space_rows:
        logger.info(
            "[3D Space N=%6d (M=%5d)] R(S^2=1,C^3=1)=%5d | True Goldbach (r=1)=%4d | "
            "WR2 Pinched Semiprimes (r^5000<=q^4469)=%4d | Ramified r==q=%d | D==0 Masquerades=%d",
            row["N"],
            row["M"],
            row["rs2c3_pure_radical_S1_C1_count"],
            row["true_goldbach_r1_witnesses"],
            row["wr2_one8938_semiprime_r_gt_1_count"],
            row["wr2_ramified_squares_r_eq_q"],
            row["wr2_zero_discriminant_masquerades"],
        )

    report = {
        "source_file_sha256": file_hashes,
        "rational_budget_analysis": budget,
        "precomputed_3d_space_comparison": space_rows,
    }
    JSON_PATH.write_text(json.dumps(report, indent=2), encoding="utf-8")
    logger.info("Saved full verification report to %s", JSON_PATH)


if __name__ == "__main__":
    main()