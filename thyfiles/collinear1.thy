theory collinear1
	imports Geometry equalitysymmetric
begin

theorem collinear1:
	assumes "axioms"
		"col A B C"
	shows "col B A C"
proof -
	have "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" using collinear_f[OF `axioms` `col A B C`] .
	consider "A = B"|"A = C"|"B = C"|"bet B A C"|"bet A B C"|"bet A C B" using `A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B`  by blast
	hence "col B A C"
	proof (cases)
		assume "A = B"
		have "B = A" using equalitysymmetric[OF `axioms` `A = B`] .
		have "col B A C" using collinear_b `axioms` `B = A` by blast
		thus ?thesis by blast
	next
		assume "A = C"
		have "col B A C" using collinear_b `axioms` `A = C` by blast
		thus ?thesis by blast
	next
		assume "B = C"
		have "col B A C" using collinear_b `axioms` `B = C` by blast
		thus ?thesis by blast
	next
		assume "bet B A C"
		have "col B A C" using collinear_b `axioms` `bet B A C` by blast
		thus ?thesis by blast
	next
		assume "bet A B C"
		have "col B A C" using collinear_b `axioms` `bet A B C` by blast
		thus ?thesis by blast
	next
		assume "bet A C B"
		have "bet B C A" using betweennesssymmetryE[OF `axioms` `bet A C B`] .
		have "col B A C" using collinear_b `axioms` `bet B C A` by blast
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end