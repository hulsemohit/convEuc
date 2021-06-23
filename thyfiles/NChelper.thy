theory NChelper
	imports Geometry collinear4 collinear5 collinearorder inequalitysymmetric
begin

theorem NChelper:
	assumes "axioms"
		"\<not> col A B C"
		"col A B P"
		"col A B Q"
		"P \<noteq> Q"
	shows "\<not> col P Q C"
proof -
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> B)"
		hence "A = B" by blast
		have "col A B C" using collinear_b `axioms` `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "col B P Q" using collinear4[OF `axioms` `col A B P` `col A B Q` `A \<noteq> B`] .
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "col B A P" using collinearorder[OF `axioms` `col A B P`] by blast
	have "col B A Q" using collinearorder[OF `axioms` `col A B Q`] by blast
	have "col A P Q" using collinear4[OF `axioms` `col B A P` `col B A Q` `B \<noteq> A`] .
	have "col P Q A" using collinearorder[OF `axioms` `col A P Q`] by blast
	have "col P Q B" using collinearorder[OF `axioms` `col B P Q`] by blast
	have "\<not> (col P Q C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col P Q C))"
hence "col P Q C" by blast
		have "col A B C" using collinear5[OF `axioms` `P \<noteq> Q` `col P Q A` `col P Q B` `col P Q C`] .
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "\<not> col P Q C" by blast
	thus ?thesis by blast
qed

end