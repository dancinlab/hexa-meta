# Imported from canon

All files in this repo were **moved** out of `dancinlab/canon` during the
canon-minimization migration. `hexa-meta` is the new home for n=6
self-referential material; canon no longer holds these (recover prior history via
`git log` in canon).

## Wave 1 — 2026-05-10 (canon@a86ca143)

- `proofs/` — 11 files ← `canon:theory/proofs/`
- `papers/` — 24 files ← `canon:papers/`
- `tools/`  — 15 dirs ← `canon:bridge/origins/`

### Excluded on import (security / hygiene)

- `tools/ready-absorber/findings/` — 40 MB of file-discovery scan output containing
  `preview` snippets of scanned files, including **live Google OAuth credentials** (a
  `gmail_credentials.json` / `gmail_token.json` that the scanner scooped up). Removed
  before publishing. (⚠️ Those credentials also live in `dancinlab/canon` history —
  see SECURITY note: rotate the Google client secret + tokens and scrub canon history.)
- `tools/ready-absorber/{state.json,phase2_state.json,verified/,growth/}` — runtime state.

## Wave 4 — 2026-05-11 (canon@50e6f679) — theory/ + formal/

n=6 영구 이론층(timeless theory layer) 통합. canon `INDEX.json`의 9축 중
`theory` 축이 통째로 hexa-meta에 흡수되었다.

### theory/ → top-level dirs (249 files)

| 도착 경로 | 출발 (canon) | 파일 수 | 내용 |
|---|---|---:|---|
| `breakthroughs/` | `canon:theory/breakthroughs/` | 6 | BT 카탈로그 (`breakthrough-theorems.md`, `bt-361-379-index.json`, `bt-candidates-*.md`, `_hypotheses_index.json`) |
| `constants/` | `canon:theory/constants/` | 5 | n=6 불변량 상수 |
| `flow/` | `canon:theory/flow/` | 4 | 워크플로우 정의 |
| `predictions/` | `canon:theory/predictions/` | 117 | 사전 등록된 예측 + `verify_SIG-*.hexa`, `bsd_*`, `kuramoto_*`, `ns_onsager_*`, `rh_triple_*`, `star_formula_*` |
| `preprints/` | `canon:theory/preprints/` | 1 | preprint draft |
| `roadmap-v2/` | `canon:theory/roadmap-v2/` | 65 | millennium-v3/v4 디자인 + `n6arch-axes/`, axis-round 01–05, final-roadmap-v2 nexus-19axis, phase 01–phase 02 |
| `roadmap-v3/` | `canon:theory/roadmap-v3/` | 3 | 차세대 roadmap |
| `study/` | `canon:theory/study/` | 48 | 연구 방법론 p0/p1/p2/p3 |

### theory/_index.json → `_theory_index.json` (1)

canon 9축 manifest의 theory 부분만 보존 (루트 `_index.json`과 충돌 회피).

### formal/lean4/ → `formal/lean4/` (10 files, `.olean` 제외)

n=6 Lean4 정형 증명:
- `N6/InvariantLattice/Sigma.lean`, `SigmaLatticeCard.lean`
- `N6/Weave/ClosureCert.lean`, `LandauerMonotonic.lean`, `PiP2Termination.lean`, `PiP2Verifier.lean`, `Strategy.lean`
- `lakefile.lean`, `lean-toolchain`, `README.md`

> Note: `.olean` 컴파일 산출물은 import에서 제외 (재생성 가능).

### Wave 4 합계
- **이관 파일**: 260 (theory 249 + _theory_index 1 + formal 10)
- **Pre-canon SHA**: `canon@50e6f679`
