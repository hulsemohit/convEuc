theory collinear2
	imports Geometry equalitysymmetric
begin

theorem collinear2:
	assumes "axioms"
		"col A B C"
	shows "col B C A"
proof -
	have "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" using collinear_f[OF `axioms` `col A B C`] .
	consider "A = B"|"A = C"|"B = C"|"bet B A C"|"bet A B C"|"bet A C B" using `A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B`  by blast
	hence "col B C A"
	proof (cases)
		assume "A = B"
		have "B = A" using equalitysymmetric[OF `axioms` `A = B`] .
		have "col B C A" using collinear_b `axioms` `B = A` by blast
		thus ?thesis by blast
	next
		assume "A = C"
		have "C = A" using equalitysymmetric[OF `axioms` `A = C`] .
		have "col B C A" using collinear_b `axioms` `C = A` by blast
		thus ?thesis by blast
	next
		assume "B = C"
		have "col B C A" using collinear_b `axioms` `B = C` by blast
		thus ?thesis by blast
	next
		assume "bet B A C"
		have "col B C A" using collinear_b `axioms` `bet B A C` by blast
		thus ?thesis by blast
	next
		assume "bet A B C"
		have "bet C B A" using betweennesssymmetryE[OF `axioms` `bet A B C`] .
		have "col B C A" using collinear_b `axioms` `bet C B A` by blast
		thus ?thesis by blast
	next
		assume "bet A C B"
		have "bet B C A" using betweennesssymmetryE[OF `axioms` `bet A C B`] .
		have "col B C A" using collinear_b `axioms` `bet B C A` by blast
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end