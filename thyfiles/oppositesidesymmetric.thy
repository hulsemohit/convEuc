theory oppositesidesymmetric
	imports Axioms Definitions Theorems
begin

theorem oppositesidesymmetric:
	assumes: `axioms`
		"oppo_side P A B Q"
	shows: "oppo_side Q A B P"
proof -
	obtain R where "bet P R Q \<and> col A B R \<and> \<not> col A B P" sorry
	have "bet P R Q" using `bet P R Q \<and> col A B R \<and> \<not> col A B P` by blast
	have "col A B R" using `bet P R Q \<and> col A B R \<and> \<not> col A B P` by blast
	have "\<not> col A B P" using `bet P R Q \<and> col A B R \<and> \<not> col A B P` by blast
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "A = B"
		have "col A B P" using col_b `axioms` `A = B` by blast
		show "False" using `col A B P` `bet P R Q \<and> col A B R \<and> \<not> col A B P` by blast
	qed
	hence "A \<noteq> B" by blast
	have "bet Q R P" using betweennesssymmetryE[OF `axioms` `bet P R Q`] .
	have "\<not> (col A B Q)"
	proof (rule ccontr)
		assume "col A B Q"
		have "col P R Q" using col_b `axioms` `bet P R Q \<and> col A B R \<and> \<not> col A B P` by blast
		have "col A B R" using `col A B R` .
		have "col B Q R" using collinear4[OF `axioms` `col A B Q` `col A B R` `A \<noteq> B`] .
		have "col Q R B" using collinearorder[OF `axioms` `col B Q R`] by blast
		have "col Q R P" using collinearorder[OF `axioms` `col P R Q`] by blast
		have "Q \<noteq> R" using betweennotequal[OF `axioms` `bet Q R P`] by blast
		have "col R B P" using collinear4[OF `axioms` `col Q R B` `col Q R P` `Q \<noteq> R`] .
		have "col R B A" using collinearorder[OF `axioms` `col A B R`] by blast
		consider "R = B"|"R \<noteq> B" by blast
		hence col A P B
		proof (cases)
			case 1
			have "col P B Q" sorry
			have "col B Q P" using collinearorder[OF `axioms` `col P B Q`] by blast
			have "col B Q A" using collinearorder[OF `axioms` `col A B Q`] by blast
			have "R \<noteq> Q" using betweennotequal[OF `axioms` `bet P R Q`] by blast
			have "B \<noteq> Q" sorry
			have "col Q P A" using collinear4[OF `axioms` `col B Q P` `col B Q A` `B \<noteq> Q`] .
			have "col Q P B" using collinearorder[OF `axioms` `col B Q P`] by blast
			have "P \<noteq> Q" using betweennotequal[OF `axioms` `bet P R Q`] by blast
			have "Q \<noteq> P" using inequalitysymmetric[OF `axioms` `P \<noteq> Q`] .
			have "col P A B" using collinear4[OF `axioms` `col Q P A` `col Q P B` `Q \<noteq> P`] .
			have "col A P B" using collinearorder[OF `axioms` `col P A B`] by blast
		next
			case 2
			have "col B P A" using collinear4[OF `axioms` `col R B P` `col R B A` `R \<noteq> B`] .
			have "col A P B" using collinearorder[OF `axioms` `col B P A`] by blast
		next
		have "col A B P" using collinearorder[OF `axioms` `col A P B`] by blast
		show "False" using `col A B P` `bet P R Q \<and> col A B R \<and> \<not> col A B P` by blast
	qed
	hence "\<not> col A B Q" by blast
	have "oppo_side Q A B P" sorry
	thus ?thesis by blast
qed

end