import LFT.Entropy

-- Expect ~1.0 for two equal counts (prints during build/elab).
#eval LFT.Entropy.shannonFromCounts [1, 1]

-- Expect ~log2 3 ≈ 1.585 for three equal counts.
#eval LFT.Entropy.shannonFromCounts [1, 1, 1]
