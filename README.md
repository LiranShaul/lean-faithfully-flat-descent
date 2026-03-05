# Faithfully Flat Descent of Projectivity in Lean 4

This repository contains a formalization of the faithfully flat descent of projectivity for modules over commutative rings. This result, originally from Raynaud and Gruson, was later corrected by Perry to fix a subtle gap regarding Mittag-Leffler conditions.

## Key Theorems Formalized

* **Theorem I (Descent):** Let $R \to S$ be a faithfully flat map of commutative rings. An $R$-module $P$ is projective if and only if $S \otimes_R P$ is projective over $S$.
* **Theorem II (Characterization):** An $R$-module $P$ is projective if and only if it is flat, Mittag-Leffler, and a direct sum of countably generated modules.
* **Kaplansky's Theorem:** Any direct summand of a direct sum of countably generated modules is itself a direct sum of countably generated modules.
* **Lazard's Theorem:** Every flat module is a direct limit of finitely presented free modules.

## Project Structure

The project consists of over 10,000 lines of new code developed for Lean 4 and Mathlib:

* `basechange.lean`: The main results, including Theorem I and Theorem II.
* `lib/Kap.lean`: Kaplansky devissage and countable generation framework.
* `lib/mlModule.lean` & `lib/mlSystem.lean`: Mittag-Leffler modules and inverse systems.
* `lib/Lazard.lean`: Proof of Lazard's theorem.
* `lib/Pushout.lean`: Concrete realization of module pushouts and their properties.
* `lib/UnivInj.lean`: Theory of universally injective maps and lifting properties.

## Requirements

This project is built using:
* **Lean 4** (see `lean-toolchain` for the specific version)
* **Mathlib 4**

