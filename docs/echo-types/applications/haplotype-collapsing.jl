# SPDX-License-Identifier: MPL-2.0
# haplotype-collapsing.jl — Julia executable shadow of EchoHaplotypeCollapsing.agda
#
# This file shows how to pass the homotopy fiber witness through the
# Julia exacts (distance) matrix without slowing down O(n²) calculations.
#
# Key idea: distance matrix is O(m²) on Haplotypes (representatives),
# fiber witness is O(n) sidecar, never in hot loop.
# Echo f y = Σ (c : Clone) (f c ≡ y) → Dict{Haplotype, Vector{Clone}}
#
# Run: julia docs/echo-types/applications/haplotype-collapsing.jl
# Test: include this file in EchoTypes.jl as EchoHaplotypeCollapsing module

# Minimal deps: only Distances.jl for Hamming, no BioJulia needed for core idea
# using Pkg; Pkg.add("Distances")
# For full Protoctist.jl integration, add BioSequences.jl, etc.

# --- Domain types (mirrors Agda Clone = ℕ × Bool, Haplotype = ℕ) ---

struct Clone
    id::String
    seq::String
    sample::String
    pcr_replicate::Int
end

struct Haplotype
    id::String
    rep_seq::String
end

struct CloneWitness
    clone_id::String
    haplotype_id::String
    sequence::String
    sample::String
    lineage::Dict{String, Any}
end

struct FiberBundle
    haplotype_id::String
    representative::Clone
    clones::Vector{Clone}  # full Echo fiber at this haplotype
    count::Int
    FiberBundle(h_id, rep, clones) = new(h_id, rep, clones, length(clones))
end

struct CollapsedResult
    representatives::Vector{Haplotype}          # size m
    fibers::Dict{String, FiberBundle}           # size m, total n clones
    distance_matrix::Matrix{Float64}            # m × m, NOT n × n
    total_clones::Int
end

# --- Collapse function (non-injective map f : Clone → Haplotype) ---

# Example: 100% identity collapse by sequence
collapse_by_seq(c::Clone) = c.seq

# Example: collapse by sample (like Agda proj₁) — forgets variant
collapse_by_sample(c::Clone) = c.sample

# --- Core: collapse_clones groups O(n), distance matrix O(m²) ---

function hamming_dist(s1::String, s2::String)::Float64
    # Simple Hamming, assumes equal length; production uses k2p / JC69
    @assert length(s1) == length(s2)
    count(c1 != c2 for (c1, c2) in zip(s1, s2)) |> Float64
end

function collapse_clones(
    clones::Vector{Clone},
    collapse_fn::Function = collapse_by_seq
)::CollapsedResult
    # 1. Group by collapse_fn: O(n) hash map
    # This is the fiber construction: Dict B → List A where f(a)=b
    groups = Dict{String, Vector{Clone}}()
    for c in clones
        h_id = collapse_fn(c)
        push!(get!(groups, h_id, Clone[]), c)
    end

    # 2. Representatives: m distinct haplotypes
    # Choose first clone's seq as representative (non-canonical choice!)
    # This non-canonicity is exactly no-canonical-clone-recovery theorem
    reps = Haplotype[]
    for (h_id, cs) in groups
        push!(reps, Haplotype(h_id, first(cs).seq))
    end
    # Sort for deterministic matrix order
    sort!(reps, by = r -> r.id)

    # 3. Fibers: sidecar, O(n) storage, NOT in hot loop
    # This is Σ B (Echo f) serialized
    fibers = Dict{String, FiberBundle}()
    for (h_id, cs) in groups
        fibers[h_id] = FiberBundle(h_id, first(cs), cs)
    end

    # 4. Distance matrix: O(m²) distance computations, ONLY on representatives
    # This is HaploDist = Haplotype → Haplotype → ℕ in Agda
    # Note: fiber witness never appears here
    m = length(reps)
    D = zeros(Float64, m, m)
    for i in 1:m
        for j in i+1:m
            d = hamming_dist(reps[i].rep_seq, reps[j].rep_seq)
            D[i, j] = D[j, i] = d
        end
    end

    CollapsedResult(reps, fibers, D, length(clones))
end

# --- Aggregation-as-fold: count monoid (mirrors EchoAggregation.sumMonoid) ---

# countAggregator in Agda: every value contributes 1 to sumMonoid
# Here: aggregate-values countAggregator clones = length clones
# aggregation-as-fold: count(vs ++ ws) = count(vs) + count(ws)

function count_clones(result::CollapsedResult)::Int
    # Fold over fibers: sum of counts = total clones
    # This is ⊕-fold sumMonoid (map countAggregator fibers)
    sum(b.count for b in values(result.fibers))
end

function test_aggregation_as_fold()
    clones1 = [Clone("C0", "ACGT", "S1", 1), Clone("C1", "ACGT", "S1", 2)]
    clones2 = [Clone("C2", "ACGG", "S2", 1)]
    r1 = collapse_clones(clones1)
    r2 = collapse_clones(clones2)
    r_all = collapse_clones(vcat(clones1, clones2))

    # Law: count(vs ++ ws) = count(vs) + count(ws)
    @assert count_clones(r_all) == count_clones(r1) + count_clones(r2)
    println("✓ aggregation-as-fold: count(vs ++ ws) = count(vs) + count(ws)")
end

# --- No-section: no canonical raise Haplotype → Clone ---

function test_no_canonical_recovery()
    clones = [
        Clone("C0", "ACGT", "S1", 1),
        Clone("C1", "ACGT", "S1", 2),  # same seq, different replicate
    ]
    result = collapse_clones(clones, collapse_by_seq)

    # Any raise function picking a representative per haplotype
    # cannot satisfy ∀ c, raise(collapse(c)) == c for all c
    # Because two distinct clones map to same haplotype
    h_id = "ACGT"
    fiber = result.fibers[h_id]
    @assert length(fiber.clones) == 2
    @assert fiber.clones[1].id != fiber.clones[2].id

    # Try to define raise: pick first clone as representative
    raise(h) = result.fibers[h].representative

    # Check: does raise(collapse(c)) == c for all c? No!
    c0 = clones[1]
    c1 = clones[2]
    @assert raise(collapse_by_seq(c0)).id == c0.id  # first happens to match
    @assert raise(collapse_by_seq(c1)).id != c1.id  # second fails — no section!

    println("✓ no-canonical-clone-recovery: no section exists (echo distinguishes clones)")
end

# --- Cost model: O(n + m²) vs O(n²) ---

function benchmark_cost_model()
    # Synthetic: n=10000 clones, m=100 distinct haplotypes (100x collapse)
    n = 10000
    m = 100
    clones = [Clone("C$i", "SEQ$(i % m)", "S$(i % 10)", i) for i in 1:n]

    # Time grouping O(n)
    t_group = @elapsed collapse_clones(clones)

    # Naive O(n²) would be 10000² = 100M distance comps
    # Our O(m²) is 100² = 10k distance comps — 10000x fewer!
    naive_comps = n * n
    our_comps = m * m
    speedup = naive_comps / our_comps

    println("Cost model:")
    println("  n = $n clones, m = $m haplotypes")
    println("  Naive O(n²): $naive_comps distance comps")
    println("  Echo sidecar O(n + m²): $(n + our_comps) ops ($n grouping + $our_comps dist)")
    println("  Speedup: $(speedup)x fewer distance comps")
    println("  Fiber sidecar: O(n) storage, not in hot loop")
end

# --- JEG display: fiber lineage without slowing matrix ---

function jeg_display_example(result::CollapsedResult)
    println("\nJEG display (haplotype graph + expandable fibers):")
    println("Nodes (m=$(length(result.representatives)) haplotypes):")
    for rep in result.representatives
        fiber = result.fibers[rep.id]
        println("  $(rep.id): $(fiber.count) clones, rep=$(fiber.representative.id)")
    end
    println("\nDistance matrix (m×m=$(size(result.distance_matrix))):")
    display(result.distance_matrix)

    # Expand one haplotype: O(k) rendering, no distance recomputation
    first_h = first(result.representatives).id
    println("\nExpanded fiber for $first_h (structural lineage):")
    for c in result.fibers[first_h].clones
        println("  $(c.id) — sample $(c.sample), replicate $(c.pcr_replicate) — Echo witness: $(first_h) == collapse($(c.id))")
    end
end

# --- Main demo ---

function main()
    println("=== Haplotype Collapsing as Echo Fiber — Julia shadow ===\n")

    clones = [
        Clone("C0", "ACGTACGT", "S1", 1),
        Clone("C1", "ACGTACGT", "S1", 2),  # same seq, different replicate → same haplotype
        Clone("C2", "ACGTACGG", "S2", 1),
        Clone("C3", "ACGTACGT", "S1", 3),  # third clone at H0
    ]

    result = collapse_clones(clones, collapse_by_seq)

    println("Collapsed $(result.total_clones) clones → $(length(result.representatives)) haplotypes")
    println("Fibers:")
    for (h_id, bundle) in result.fibers
        println("  $h_id: $(bundle.count) clones — $(join([c.id for c in bundle.clones], ", "))")
    end

    println("\nDistance matrix (O(m²) on haplotypes, not clones):")
    display(result.distance_matrix)

    test_aggregation_as_fold()
    test_no_canonical_recovery()
    benchmark_cost_model()
    jeg_display_example(result)

    println("\n=== Done — Echo fiber witness preserved without slowing O(m²) ===")
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
