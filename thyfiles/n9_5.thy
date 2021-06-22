theory n9_5
	imports Axioms Definitions Theorems
begin

theorem n9_5:
	assumes: `axioms`
		"oppo_side P A B C"
		"ray_on R Q P"
		"col A B R"
	shows: "oppo_side Q A B C"
proof -
	have "bet R P Q \<or> Q = P \<or> bet R Q P" using ray1[OF `axioms` `ray_on R Q P`] .
	consider "\<not> col C P R"|"col C P R" by blast
	hence oppo_side Q A B C
	proof (cases)
		case 1
		consider "bet R P Q"|"Q = P"|"bet R Q P" using `bet R P Q \<or> Q = P \<or> bet R Q P`  by blast
		hence oppo_side Q A B C
		proof (cases)
			case 1
			have "\<not> (col R Q C)"
			proof (rule ccontr)
				assume "col R Q C"
				have "col Q R C" using collinearorder[OF `axioms` `col R Q C`] by blast
				have "col R Q P" using rayimpliescollinear[OF `axioms` `ray_on R Q P`] .
				have "col Q R P" using collinearorder[OF `axioms` `col R Q P`] by blast
				have "R \<noteq> Q" using betweennotequal[OF `axioms` `bet R P Q`] by blast
				have "Q \<noteq> R" using inequalitysymmetric[OF `axioms` `R \<noteq> Q`] .
				have "col R C P" using collinear4[OF `axioms` `col Q R C` `col Q R P` `Q \<noteq> R`] .
				have "col C P R" using collinearorder[OF `axioms` `col R C P`] by blast
				have "\<not> col C P R" using `\<not> col C P R` .
				show "False" using `\<not> col C P R` `col C P R` by blast
			qed
			hence "\<not> col R Q C" by blast
			have "oppo_side Q A B C" using n9_5a[OF `axioms` `oppo_side P A B C` `bet R P Q` `\<not> col R Q C` `col A B R`] .
		next
			case 2
			have "oppo_side Q A B C" sorry
		next
			case 3
			have "oppo_side Q A B C" using n9_5b[OF `axioms` `oppo_side P A B C` `bet R Q P` `\<not> col C P R` `col A B R`] .
		next
	next
		case 2
		obtain L where "bet P L C \<and> col A B L \<and> \<not> col A B P" sorry
		have "bet P L C" using `bet P L C \<and> col A B L \<and> \<not> col A B P` by blast
		have "col A B L" using `bet P L C \<and> col A B L \<and> \<not> col A B P` by blast
		have "\<not> col A B P" using `bet P L C \<and> col A B L \<and> \<not> col A B P` by blast
		have "col P C L" using col_b `axioms` `bet P L C \<and> col A B L \<and> \<not> col A B P` by blast
		have "col C P L" using collinearorder[OF `axioms` `col P C L`] by blast
		have "P \<noteq> C" using betweennotequal[OF `axioms` `bet P L C`] by blast
		have "C \<noteq> P" using inequalitysymmetric[OF `axioms` `P \<noteq> C`] .
		have "col P L R" using collinear4[OF `axioms` `col C P L` `col C P R` `C \<noteq> P`] .
		have "\<not> (A = B)"
		proof (rule ccontr)
			assume "A = B"
			have "col A B P" using col_b `axioms` `A = B` by blast
			show "False" using `col A B P` `bet P L C \<and> col A B L \<and> \<not> col A B P` by blast
		qed
		hence "A \<noteq> B" by blast
		have "col B L R" using collinear4[OF `axioms` `col A B L` `col A B R` `A \<noteq> B`] .
		have "col L R P" using collinearorder[OF `axioms` `col P L R`] by blast
		have "col L R B" using collinearorder[OF `axioms` `col B L R`] by blast
		have "\<not> (L \<noteq> R)"
		proof (rule ccontr)
			assume "L \<noteq> R"
			have "col R P B" using collinear4[OF `axioms` `col L R P` `col L R B` `L \<noteq> R`] .
			have "col R B P" using collinearorder[OF `axioms` `col R P B`] by blast
			have "col R B A" using collinearorder[OF `axioms` `col A B R`] by blast
			have "\<not> (R \<noteq> B)"
			proof (rule ccontr)
				assume "R \<noteq> B"
				have "col B P A" using collinear4[OF `axioms` `col R B P` `col R B A` `R \<noteq> B`] .
				have "col A B P" using collinearorder[OF `axioms` `col B P A`] by blast
				have "\<not> col A B P" using `\<not> col A B P` .
				show "False" using `\<not> col A B P` `col A B P` by blast
			qed
			hence "R = B" by blast
			have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
			have "R \<noteq> A" sorry
			have "col B A R" using collinearorder[OF `axioms` `col A B R`] by blast
			have "col B A L" using collinearorder[OF `axioms` `col A B L`] by blast
			have "col A L R" using collinear4[OF `axioms` `col B A L` `col B A R` `B \<noteq> A`] .
			have "col L R A" using collinearorder[OF `axioms` `col A L R`] by blast
			have "col R P A" using collinear4[OF `axioms` `col L R P` `col L R A` `L \<noteq> R`] .
			have "col R A P" using collinearorder[OF `axioms` `col R P A`] by blast
			have "col R A B" using collinearorder[OF `axioms` `col A B R`] by blast
			have "col A P B" using collinear4[OF `axioms` `col R A P` `col R A B` `R \<noteq> A`] .
			have "col A B P" using collinearorder[OF `axioms` `col A P B`] by blast
			have "\<not> col A B P" using `\<not> col A B P` .
			show "False" using `\<not> col A B P` `col A B P` by blast
		qed
		hence "L = R" by blast
		have "bet P R C" sorry
		have "bet C R P" using betweennesssymmetryE[OF `axioms` `bet P R C`] .
		consider "bet R P Q"|"Q = P"|"bet R Q P" using `bet R P Q \<or> Q = P \<or> bet R Q P`  by blast
		hence bet C R Q
		proof (cases)
			case 1
			have "bet C R Q" using n3_7b[OF `axioms` `bet C R P` `bet R P Q`] .
		next
			case 2
			have "bet C R Q" sorry
		next
			case 3
			have "bet C R Q" using innertransitivityE[OF `axioms` `bet C R P` `bet R Q P`] .
		next
		have "bet Q R C" using betweennesssymmetryE[OF `axioms` `bet C R Q`] .
		have "\<not> (col A B Q)"
		proof (rule ccontr)
			assume "col A B Q"
			have "col A B R" using `col A B R` .
			have "col B Q R" using collinear4[OF `axioms` `col A B Q` `col A B R` `A \<noteq> B`] .
			have "col R Q P" using rayimpliescollinear[OF `axioms` `ray_on R Q P`] .
			have "col Q R B" using collinearorder[OF `axioms` `col B Q R`] by blast
			have "col Q R P" using collinearorder[OF `axioms` `col R Q P`] by blast
			have "Q \<noteq> R" using betweennotequal[OF `axioms` `bet Q R C`] by blast
			have "col R B P" using collinear4[OF `axioms` `col Q R B` `col Q R P` `Q \<noteq> R`] .
			have "col R B A" using collinearorder[OF `axioms` `col A B R`] by blast
			have "\<not> (R \<noteq> B)"
			proof (rule ccontr)
				assume "R \<noteq> B"
				have "col B P A" using collinear4[OF `axioms` `col R B P` `col R B A` `R \<noteq> B`] .
				have "col A B P" using collinearorder[OF `axioms` `col B P A`] by blast
				have "\<not> col A B P" using `\<not> col A B P` .
				show "False" using `\<not> col A B P` `col A B P` by blast
			qed
			hence "R = B" by blast
			have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
			have "R \<noteq> A" sorry
			have "col B A R" using collinearorder[OF `axioms` `col A B R`] by blast
			have "col B A Q" using collinearorder[OF `axioms` `col A B Q`] by blast
			have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
			have "col A Q R" using collinear4[OF `axioms` `col B A Q` `col B A R` `B \<noteq> A`] .
			have "col Q R A" using collinearorder[OF `axioms` `col A Q R`] by blast
			have "col Q R P" using `col Q R P` .
			have "col R A P" using collinear4[OF `axioms` `col Q R A` `col Q R P` `Q \<noteq> R`] .
			have "col R A B" using collinearorder[OF `axioms` `col A B R`] by blast
			have "col A P B" using collinear4[OF `axioms` `col R A P` `col R A B` `R \<noteq> A`] .
			have "col A B P" using collinearorder[OF `axioms` `col A P B`] by blast
			have "\<not> col A B P" using `\<not> col A B P` .
			show "False" using `\<not> col A B P` `col A B P` by blast
		qed
		hence "\<not> col A B Q" by blast
		have "bet Q R C \<and> col A B R \<and> \<not> col A B Q" using `bet Q R C` `col A B R` `\<not> col A B Q` by blast
		have "oppo_side Q A B C" sorry
	next
	thus ?thesis by blast
qed

end