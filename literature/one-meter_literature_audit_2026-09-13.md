# One-meter all-car-count formula: bounded literature comparison

## Conclusion and limits

The displayed all-length generating function and explicit binomial-coefficient recurrence were **not found stated in the original paper or public records inspected on 2026-09-13**. They follow by eliminating the last-outcome states used in the source paper, whose local transition argument applies at every prefix length.

This is a bounded comparison, **not** an exhaustive literature review, first-solution claim, priority determination, or evidence of journal acceptance or external human peer review. An equivalent formula could occur under different terminology, in an unindexed or inaccessible publication, or in unpublished work. Formal verification proves the stated mathematics under its foundations; it does not establish novelty.

## Original source and the precise additional range

Spencer Daugherty, Pamela E. Harris, Ian Klein and Matt McClinton, *Metered Parking Functions*, **Integers 25** (2025), A73, DOI [10.5281/zenodo.16881806](https://doi.org/10.5281/zenodo.16881806), preprint [arXiv:2406.12941](https://arxiv.org/abs/2406.12941).

The page references below use the journal PDF's printed pages:

- **Pages 14–15, Theorem 2 and its argument:** the Lucas recurrence is proved through car count `m=n+1`. The proof decomposes successful extensions by the last parking outcome. The same local rule gives the state equation for arbitrary nonempty prefix length.
- **Pages 16–17, Corollary 5:** the radical closed form explicitly requires `m≤n+1` and `n>2`.
- **Pages 17–18, Proposition 6:** all lengths for `n=2` are already treated, with `F_m(2)=2F_(m−2)(2)` for `m>2` and the stated initial values.
- **Page 32, Problem 2:** asks for a recursive or closed formula for one-metered `(m,n)`-parking functions when `m>n`.

Thus capacities one and two and the Lucas range through `m=n+1` are not new coverage. The additional range addressed by the general formula is **`n≥3,m≥n+2`**. No minimal recurrence-order claim is made.

## Formula and attribution

The [separate note](../one-meter/main.md) attributes the model and starting decomposition to the original authors. For the actual successful ordered-preference count, it derives

\[
G_n(X)=\sum_{m\ge0}F_m(n)X^m
=\frac{(1+X)^n}{(1-nX+X^2)(1+X)^n-X^{n+2}}.
\]

With `c(n,j)=n·choose(n,j−1)−choose(n,j)−choose(n,j−2)`, the scalar recurrence is

\[
F_m(n)=\sum_{j=2}^{n}c(n,j)F_{m-j}(n)\qquad(m\ge n+1).
\]

Initial counts and the bounded Lucas relation supply sufficient initial data. The first correction beyond that range is exactly
`F_(n+2)=nF_(n+1)−F_n+1`. This is an explicit mathematical answer to Problem 2, derived from the cited decomposition, without a priority claim. The companion Lean proof checks these statements for the original preference-count definition; it uses division-free state elimination instead of the note's weighted geometric-sum presentation.

## Inspected public records

The following records and queries were fetched or attempted on **2026-09-13**. Counts describe those responses, not current or complete indexing. The decisive original journal pages 14–18 and 32 were also inspected directly.

| Source/query | Observed response | Limitation |
|---|---|---|
| General exact-title/authors/citation web search | HTTP 402; service credits unavailable | Search unavailable, not negative evidence. |
| OpenAlex general title search, first 10 | HTTP 200; mostly transportation-engineering matches | Low specificity. |
| Crossref title query, first 10 | HTTP 200; mostly different parking/transport titles | No equivalent found in these results; not exhaustive. |
| OpenAlex exact-title filter | One matching preprint, `W4399912054` | Original record located. |
| OpenAlex preprint DOI `10.48550/arXiv.2406.12941` | Same preprint; cited-by count zero, empty reference metadata | Incomplete metadata limits citation coverage. |
| OpenAlex journal DOI `10.5281/zenodo.16881806` | Separate record `W6968592069`; cited-by count zero, empty references | Both versions checked rather than assuming deduplication. |
| OpenAlex citations to either record | Empty result set | No indexed citation returned, not proof of no follow-up. |
| Semantic Scholar exact arXiv lookup and citations | Correct paper; citation count zero and empty citation list | Same indexing limitation. |
| OpenAlex title search `metered parking`, first 50 | 188 total matches; only 50 inspected, mostly transportation engineering plus the original preprint | Remaining 138 were not inspected. |
| arXiv abstract/version record | Only v1 observed; unchanged from the earlier fetched record | Not an exhaustive arXiv search. |
| Daugherty research page | Original paper and OEIS links; no separate all-length follow-up identified | Limited to that page. |
| OEIS A372817 text | Its table includes `F_5(3)=145` | The unqualified Lucas expression cannot be continued to that value; the original paper's bounded theorem remains valid. |
| arXiv web and export-API searches | HTTP 429 | Searches unavailable, not empty results. |

No cause is assigned to the OEIS presentation, and no public correction or author contact is represented by this audit.

## Public source locations

- [Journal PDF](https://math.colgate.edu/~integers/z73/z73.pdf)
- [arXiv abstract](https://arxiv.org/abs/2406.12941)
- [OEIS A372817](https://oeis.org/A372817)
- [Daugherty research page](https://spdaugherty.github.io/research.html)

## Separate verification boundary

The [formalization record](../verification/one-meter/LEAN.md) describes the actual-count Lean theorem, its checks, and trust assumptions. The [finite checker](../verification/one-meter/check_counts.py) covers 586,023 ordered inputs for `n=1..5,m=0..8` and compares state/scalar counts for `n=1..20,m=0..40`. Neither finite agreement nor internal AI review is evidence of priority; the finite checks are not the all-parameter proof.
