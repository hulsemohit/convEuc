theory collinear1
	imports Axioms Definitions Theorems
begin

theorem collinear1:
	assumes: `axioms`
		"col A B C"
	shows: "col B A C"
proof -
	have "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" using collinear_f[OF `axioms` `col A B C`] .
	consider "A = B"|"A = C"|"B = C"|"bet B A C"|"bet A B C"|"bet A C B" using `A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B`  by blast
	hence col B A C
	proof (cases)
		case 1
		have "B = A" using equalitysymmetric[OF `axioms` `A = B`] .
		have "col B A C" using collinear_b `axioms` `B = A` by blast
	next
		case 2
		have "col B A C" using collinear_b `axioms` `A = C` by blast
	next
		case 3
		have "col B A C" using collinear_b `axioms` `B = C` by blast
	next
		case 4
		have "col B A C" using collinear_b `axioms` `bet B A C` by blast
	next
		case 5
		have "col B A C" using collinear_b `axioms` `bet A B C` by blast
	next
		case 6
		have "bet B C A" using betweennesssymmetryE[OF `axioms` `bet A C B`] .
		have "col B A C" using collinear_b `axioms` `bet B C A` by blast
	next
	thus ?thesis by blast
qed

end