theory twolines2
	imports Axioms Definitions Theorems
begin

theorem twolines2:
	assumes: `axioms`
		"A \<noteq> B"
		"C \<noteq> D"
		"col P A B"
		"col P C D"
		"col Q A B"
		"col Q C D"
		"\<not> (col A C D \<and> col B C D)"
	shows: "P = Q"
proof -
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "D \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> D`] .
	have "\<not> (P \<noteq> Q)"
	proof (rule ccontr)
		assume "P \<noteq> Q"
		have "col D C P" using collinearorder[OF `axioms` `col P C D`] by blast
		have "col D C Q" using collinearorder[OF `axioms` `col Q C D`] by blast
		have "col C P Q" using collinear4[OF `axioms` `col D C P` `col D C Q` `D \<noteq> C`] .
		have "col A B P" using collinearorder[OF `axioms` `col P A B`] by blast
		have "col A B Q" using collinearorder[OF `axioms` `col Q A B`] by blast
		have "col B P Q" using collinear4[OF `axioms` `col A B P` `col A B Q` `A \<noteq> B`] .
		have "col P Q B" using collinearorder[OF `axioms` `col B P Q`] by blast
		have "col C P Q" using `col C P Q` .
		have "col P Q C" using collinearorder[OF `axioms` `col C P Q`] by blast
		have "col Q C B" using collinear4[OF `axioms` `col P Q C` `col P Q B` `P \<noteq> Q`] .
		have "col Q C D" using collinearorder[OF `axioms` `col D C Q`] by blast
		have "\<not> (Q = C)"
		proof (rule ccontr)
			assume "Q = C"
			have "col C P D" using collinearorder[OF `axioms` `col D C P`] by blast
			have "col Q P B" using collinearorder[OF `axioms` `col B P Q`] by blast
			have "col B A Q" using collinearorder[OF `axioms` `col A B Q`] by blast
			have "col B A P" using collinearorder[OF `axioms` `col A B P`] by blast
			have "col A Q P" using collinear4[OF `axioms` `col B A Q` `col B A P` `B \<noteq> A`] .
			have "col Q P A" using collinearorder[OF `axioms` `col A Q P`] by blast
			have "col C P B" sorry
			have "col C P A" sorry
			have "col P C A" using collinearorder[OF `axioms` `col C P A`] by blast
			have "col P C B" using collinearorder[OF `axioms` `col C P B`] by blast
			have "col P C D" using collinearorder[OF `axioms` `col C P D`] by blast
			have "\<not> (P = C)"
			proof (rule ccontr)
				assume "P = C"
				have "P = Q" sorry
				show "False" using `P = Q` `P \<noteq> Q` by blast
			qed
			hence "P \<noteq> C" by blast
			have "col C D A" using collinear4[OF `axioms` `col P C D` `col P C A` `P \<noteq> C`] .
			have "col C D B" using collinear4[OF `axioms` `col P C D` `col P C B` `P \<noteq> C`] .
			have "col A C D" using collinearorder[OF `axioms` `col C D A`] by blast
			have "col B C D" using collinearorder[OF `axioms` `col C D B`] by blast
			have "col A C D \<and> col B C D" using `col A C D` `col B C D` by blast
			show "False" using `col A C D \<and> col B C D` `\<not> (col A C D \<and> col B C D)` by blast
		qed
		hence "Q \<noteq> C" by blast
		have "col C B D" using collinear4[OF `axioms` `col Q C B` `col Q C D` `Q \<noteq> C`] .
		have "col B C D" using collinearorder[OF `axioms` `col C B D`] by blast
		have "\<not> (B = A)"
		proof (rule ccontr)
			assume "B = A"
			have "A = B" using equalitysymmetric[OF `axioms` `B = A`] .
			show "False" using `A = B` `A \<noteq> B` by blast
		qed
		hence "B \<noteq> A" by blast
		have "col B A P" using collinearorder[OF `axioms` `col A B P`] by blast
		have "col B A Q" using collinearorder[OF `axioms` `col A B Q`] by blast
		have "col A P Q" using collinear4[OF `axioms` `col B A P` `col B A Q` `B \<noteq> A`] .
		have "col P Q A" using collinearorder[OF `axioms` `col A P Q`] by blast
		have "col C P Q" using `col C P Q` .
		have "col P Q C" using collinearorder[OF `axioms` `col C P Q`] by blast
		have "col Q C A" using collinear4[OF `axioms` `col P Q C` `col P Q A` `P \<noteq> Q`] .
		have "col Q C D" using collinearorder[OF `axioms` `col D C Q`] by blast
		have "col C A D" using collinear4[OF `axioms` `col Q C A` `col Q C D` `Q \<noteq> C`] .
		have "col A C D" using collinearorder[OF `axioms` `col C A D`] by blast
		have "col A C D \<and> col B C D" using `col A C D` `col B C D` by blast
		show "False" using `col A C D \<and> col B C D` `\<not> (col A C D \<and> col B C D)` by blast
	qed
	hence "P = Q" by blast
	thus ?thesis by blast
qed

end