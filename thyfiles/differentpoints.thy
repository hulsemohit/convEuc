theory differentpoints
	imports Axioms Definitions Theorems
begin

theorem differentpoints:
	assumes: `axioms`
		"A \<noteq> B"
		"col A B C"
		"col A B D"
	shows: "\<exists> PR PR. seg_eq B P B R"
proof -
