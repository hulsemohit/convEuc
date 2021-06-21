theory collinear2
	imports Axioms Definitions Theorems
begin

theorem collinear2:
	assumes: `axioms`
		"col A B C"
	shows: "col B C A"
proof -
	have "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" sorry
