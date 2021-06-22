theory collinear2
	imports Axioms Definitions Theorems
begin

theorem collinear2:
	assumes: `axioms`
		"col A B C"
	shows: "col B C A"
proof -
	have "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" using collinear_f[OF `axioms` `col A B C`] .
	consider "A = B"|"A = C"|"B = C"|"bet B A C"|"bet A B C"|"bet A C B" using `A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B`  by blast
	hence col B C A
	proof (cases)
		case 1
		have "B = A" using equalitysymmetric[OF `axioms` `A = B`] .
		have "col B C A" using collinear_b `axioms` `B = A` by blast
	next
		case 2
		have "C = A" using equalitysymmetric[OF `axioms` `A = C`] .
		have "col B C A" using collinear_b `axioms` `C = A` by blast
	next
		case 3
		have "col B C A" using collinear_b `axioms` `B = C` by blast
	next
		case 4
		have "col B C A" using collinear_b `axioms` `bet B A C` by blast
	next
		case 5
		have "bet C B A" using betweennesssymmetryE[OF `axioms` `bet A B C`] .
		have "col B C A" using collinear_b `axioms` `bet C B A` by blast
	next
		case 6
		have "bet B C A" using betweennesssymmetryE[OF `axioms` `bet A C B`] .
		have "col B C A" using collinear_b `axioms` `bet B C A` by blast
	next
	thus ?thesis by blast
qed

end