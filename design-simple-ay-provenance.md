# Design: simple ay provenance (kill the env-surgery)

The strict gate's ay-provenance check forces "env surgery" (git-pin ay + regenerate
~25 fixture lockfiles) just to record a promotion. That rigidity is **unnecessary**:
`VerifiedSiblingPath` already derives a sound, unspoofable ay identity. Three bolted-on
clauses cause the pain; remove them, keep the integrity goal. From a read-only design
swarm (2026-06-03).

## The integrity goal (preserve exactly)
Identify *which* ay build produced the proofs and prevent claiming `Proven` with an
unknown/locally-modified/tampered ay. `VerifiedSiblingPath` meets this: `pinned_rev =
git rev-parse HEAD` of a worktree verified to (a) be the canonical `../ay` sibling
(one shared worktree root for all 4 `REQUIRED_AY_CRATES`), (b) have origin URL ==
canonical ay, (c) be **git-clean** (HEAD is a faithful content commitment to the bytes
compiled). No hand-editable lockfile string can forge this. Live verification still
re-runs every case (verdict + min_obligations + fingerprints), so a pin never
substitutes for a proof.

## The three unnecessary rigidities (the env-surgery cause)
1. **`HEAD == origin/main` hard requirement** (`verified_sibling_ay_dependency_model`,
   evidence.rs:11613-11619): a *clean* local ay that's merely ahead of origin/main
   degrades to `Unverified`. Forces resetting/pushing `../ay` to verify.
2. **Per-fixture rev-matching of a `[patch]`-overridden rev**: the 17 `cargo_*`
   fixtures each ship a `Cargo.lock` pinning ay to a frozen `git+rev` (`12ff0250…`)
   that **cargo never uses** — the root `[patch."…ay.git"]` redirects all ay to
   `../ay`. `cargo_fixture_lockfile_check` (:2152) flags that irrelevant rev as
   `stale_revs`.
3. **The sanctioned dev `[patch]` treated as disqualifying** (`active_local_ay_patch_detected`,
   :11703): the very redirect that makes the dev checkout use `../ay` fails the
   "latest private ay pin" gate (:1300).

## The simple model
Make **Path** (the renamed `VerifiedSiblingPath`) a **first-class, PASS-eligible**
identity (not a fallback), under the SAME soundness conditions (single canonical
`../ay` worktree root, origin == canonical ay, **clean** worktree). Then:
- **Drop `HEAD == origin/main`** as a hard failure. Replace with a *non-fatal*
  `ay_published` classification (`Reachable` if origin/main contains HEAD via
  `merge-base`/`branch -r --contains`, else `LocalOnly`) recorded in the evidence.
  Keep the **clean-worktree** and **origin-URL** checks (those ARE integrity).
- **Recognize the `[patch."…ay.git"]` → `../ay` redirect as sanctioned** (only when
  all patch targets resolve under the same verified `../ay` root) — not a
  disqualifier.
- **Under the Path model, accept fixture ay lock sources that are null/path/git+rev**
  — the `[patch]` means cargo uses `../ay` regardless, so the fixture's recorded ay
  rev is irrelevant to which ay actually ran. The binding lives in the root Path
  identity, not 25 lockfiles.
- Emit `ay_identity_rev` / `ay_repo_root` / `ay_origin_url` / `ay_worktree_clean` /
  `ay_published` into the JSON evidence so an auditor sees exactly which ay ran.

## Why integrity is preserved
The identity strength is unchanged: a clean canonical `../ay` HEAD, origin-verified.
`ay_published` is *reported*, not required (a clean local-ahead ay is a perfectly
knowable identity — you just record it isn't on origin yet). Fixtures no longer
self-describe ay; the single root Path identity does — and live verification still
re-checks every proof. A `Proven` claim is still tied to a known, clean ay.

## First increment (smallest, highest-leverage)
In `verified_sibling_ay_dependency_model` (evidence.rs:11613-11619): delete the
`HEAD == origin/main` hard failure; compute `ay_published` (Reachable/LocalOnly) and
carry it on the repo struct, KEEPING clean-worktree + origin-URL checks. Then in
`ay_latest_private_main_matches`/the latest-pin gate (:1300, :11439): under Path,
pass on identity (clean canonical sibling) instead of requiring `pinned_rev ==
ls-remote origin/main`. Tests: split the `requires_clean_origin_main` test into
`dirty => Unverified` (keep) and `clean-but-ahead => Path identity, ay_published=LocalOnly`.

## Risks
- `ay_published` reachability needs up-to-date remote refs; on stale/absent refs,
  classify `LocalOnly` (never fail) — it's informational.
- The `[patch]` "sanctioned" recognition must be tightly scoped to patches whose
  targets all resolve under the verified `../ay` root.
- Regenerating fixture locks to null/path ay sources is optional (the Path model
  accepts their git+rev too); if done, keep them git-tracked.

NEVER weaken what `Proven` requires: `--strict` + all run flags + every case passing
live. This only changes how the ay *identity* is established, making the normal
dev (path-dep) checkout a first-class verifiable environment.
