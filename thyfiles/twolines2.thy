theory twolines2
	imports Geometry collinear4 collinearorder equalitysymmetric inequalitysymmetric
begin

theorem(in euclidean_geometry) twolines2:
	assumes 
		"A \<noteq> B"
		"C \<noteq> D"
		"col P A B"
		"col P C D"
		"col Q A B"
		"col Q C D"
		"\<not> (col A C D \<and> col B C D)"
	shows "P = Q"
proof -
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	have "D \<noteq> C" using inequalitysymmetric[OF `C \<noteq> D`] .
	have "\<not> (P \<noteq> Q)"
	proof (rule ccontr)
		assume "\<not> (\<not> (P \<noteq> Q))"
hence "P \<noteq> Q" by blast
		have "col D C P" using collinearorder[OF `col P C D`] by blast
		have "col D C Q" using collinearorder[OF `col Q C D`] by blast
		have "col C P Q" using collinear4[OF `col D C P` `col D C Q` `D \<noteq> C`] .
		have "col A B P" using collinearorder[OF `col P A B`] by blast
		have "col A B Q" using collinearorder[OF `col Q A B`] by blast
		have "col B P Q" using collinear4[OF `col A B P` `col A B Q` `A \<noteq> B`] .
		have "col P Q B" using collinearorder[OF `col B P Q`] by blast
		have "col C P Q" using `col C P Q` .
		have "col P Q C" using collinearorder[OF `col C P Q`] by blast
		have "col Q C B" using collinear4[OF `col P Q C` `col P Q B` `P \<noteq> Q`] .
		have "col Q C D" using collinearorder[OF `col D C Q`] by blast
		have "\<not> (Q = C)"
		proof (rule ccontr)
			assume "\<not> (Q \<noteq> C)"
			hence "Q = C" by blast
			have "col C P D" using collinearorder[OF `col D C P`] by blast
			have "col Q P B" using collinearorder[OF `col B P Q`] by blast
			have "col B A Q" using collinearorder[OF `col A B Q`] by blast
			have "col B A P" using collinearorder[OF `col A B P`] by blast
			have "col A Q P" using collinear4[OF `col B A Q` `col B A P` `B \<noteq> A`] .
			have "col Q P A" using collinearorder[OF `col A Q P`] by blast
			have "col C P B" using `col Q P B` `Q = C` by blast
			have "col C P A" using `col Q P A` `Q = C` by blast
			have "col P C A" using collinearorder[OF `col C P A`] by blast
			have "col P C B" using collinearorder[OF `col C P B`] by blast
			have "col P C D" using collinearorder[OF `col C P D`] by blast
			have "\<not> (P = C)"
			proof (rule ccontr)
				assume "\<not> (P \<noteq> C)"
				hence "P = C" by blast
				have "P = Q" using `P = C` `Q = C` by blast
				show "False" using `P = Q` `P \<noteq> Q` by blast
			qed
			hence "P \<noteq> C" by blast
			have "col C D A" using collinear4[OF `col P C D` `col P C A` `P \<noteq> C`] .
			have "col C D B" using collinear4[OF `col P C D` `col P C B` `P \<noteq> C`] .
			have "col A C D" using collinearorder[OF `col C D A`] by blast
			have "col B C D" using collinearorder[OF `col C D B`] by blast
			have "col A C D \<and> col B C D" using `col A C D` `col B C D` by blast
			show "False" using `col A C D \<and> col B C D` `\<not> (col A C D \<and> col B C D)` by blast
		qed
		hence "Q \<noteq> C" by blast
		have "col C B D" using collinear4[OF `col Q C B` `col Q C D` `Q \<noteq> C`] .
		have "col B C D" using collinearorder[OF `col C B D`] by blast
		have "\<not> (B = A)"
		proof (rule ccontr)
			assume "\<not> (B \<noteq> A)"
			hence "B = A" by blast
			have "A = B" using equalitysymmetric[OF `B = A`] .
			show "False" using `A = B` `A \<noteq> B` by blast
		qed
		hence "B \<noteq> A" by blast
		have "col B A P" using collinearorder[OF `col A B P`] by blast
		have "col B A Q" using collinearorder[OF `col A B Q`] by blast
		have "col A P Q" using collinear4[OF `col B A P` `col B A Q` `B \<noteq> A`] .
		have "col P Q A" using collinearorder[OF `col A P Q`] by blast
		have "col C P Q" using `col C P Q` .
		have "col P Q C" using collinearorder[OF `col C P Q`] by blast
		have "col Q C A" using collinear4[OF `col P Q C` `col P Q A` `P \<noteq> Q`] .
		have "col Q C D" using collinearorder[OF `col D C Q`] by blast
		have "col C A D" using collinear4[OF `col Q C A` `col Q C D` `Q \<noteq> C`] .
		have "col A C D" using collinearorder[OF `col C A D`] by blast
		have "col A C D \<and> col B C D" using `col A C D` `col B C D` by blast
		show "False" using `col A C D \<and> col B C D` `\<not> (col A C D \<and> col B C D)` by blast
	qed
	hence "P = Q" by blast
	thus ?thesis by blast
qed

end