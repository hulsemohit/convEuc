theory n9_5b
	imports Axioms Definitions Theorems
begin

theorem n9_5b:
	assumes: `axioms`
		"oppo_side P A B C"
		"bet R Q P"
		"\<not> col C P R"
		"col A B R"
	shows: "oppo_side Q A B C"
proof -
	obtain S where "bet P S C \<and> col A B S \<and> \<not> col A B P" sorry
	have "bet P S C" using `bet P S C \<and> col A B S \<and> \<not> col A B P` by blast
	have "\<not> col A B P" using `bet P S C \<and> col A B S \<and> \<not> col A B P` by blast
	have "bet C S P" using betweennesssymmetryE[OF `axioms` `bet P S C`] .
	obtain F where "bet C F Q \<and> bet R F S" using Pasch-innerE[OF `axioms` `bet C S P` `bet R Q P` `\<not> col C P R`]  by  blast
	have "bet C F Q" using `bet C F Q \<and> bet R F S` by blast
	have "bet R F S" using `bet C F Q \<and> bet R F S` by blast
	have "col R S F" using col_b `axioms` `bet C F Q \<and> bet R F S` by blast
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "A = B"
		have "col A B P" using col_b `axioms` `A = B` by blast
		show "False" using `col A B P` `bet P S C \<and> col A B S \<and> \<not> col A B P` by blast
	qed
	hence "A \<noteq> B" by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "col A B R" using `col A B R` .
	have "col A B S" using `bet P S C \<and> col A B S \<and> \<not> col A B P` by blast
	have "col B R S" using collinear4[OF `axioms` `col A B R` `col A B S` `A \<noteq> B`] .
	have "col R S B" using collinearorder[OF `axioms` `col B R S`] by blast
	have "R \<noteq> S" using betweennotequal[OF `axioms` `bet R F S`] by blast
	have "col S F B" using collinear4[OF `axioms` `col R S F` `col R S B` `R \<noteq> S`] .
	have "col S B A" using collinearorder[OF `axioms` `col A B S`] by blast
	have "col S B F" using collinearorder[OF `axioms` `col S F B`] by blast
	consider "S = B"|"S \<noteq> B" by blast
	hence col A B F
	proof (cases)
		case 1
		have "col R S F" using col_b `axioms` `bet C F Q \<and> bet R F S` by blast
		have "col R B F" sorry
		have "col R B A" using collinearorder[OF `axioms` `col A B R`] by blast
		have "\<not> (R = B)"
		proof (rule ccontr)
			assume "R = B"
			have "bet R F S" using `bet R F S` .
			have "R \<noteq> S" using betweennotequal[OF `axioms` `bet R F S`] by blast
			have "R \<noteq> B" sorry
			show "False" using `R \<noteq> B` `R = B` by blast
		qed
		hence "R \<noteq> B" by blast
		have "col B F A" using collinear4[OF `axioms` `col R B F` `col R B A` `R \<noteq> B`] .
		have "col A B F" using collinearorder[OF `axioms` `col B F A`] by blast
	next
		case 2
		have "col B A F" using collinear4[OF `axioms` `col S B A` `col S B F` `S \<noteq> B`] .
		have "col A B F" using collinearorder[OF `axioms` `col B A F`] by blast
	next
	have "\<not> (col A B Q)"
	proof (rule ccontr)
		assume "col A B Q"
		have "col A B R" using `col A B R` .
		have "col B Q R" using collinear4[OF `axioms` `col A B Q` `col A B R` `A \<noteq> B`] .
		have "col B R Q" using collinearorder[OF `axioms` `col B Q R`] by blast
		have "col A B R" using `col A B R` .
		have "col A B F" using `col A B F` .
		have "col B R F" using collinear4[OF `axioms` `col A B R` `col A B F` `A \<noteq> B`] .
		consider "B = R"|"B \<noteq> R" by blast
		hence col R Q F
		proof (cases)
			case 1
			have "\<not> (A = R)"
			proof (rule ccontr)
				assume "A = R"
				have "A = B" sorry
				show "False" using `A = B` `A \<noteq> B` by blast
			qed
			hence "A \<noteq> R" by blast
			have "col B A R" using collinearorder[OF `axioms` `col A B R`] by blast
			have "col B A F" using collinearorder[OF `axioms` `col A B F`] by blast
			have "col A R F" using collinear4[OF `axioms` `col B A R` `col B A F` `B \<noteq> A`] .
			have "col B A Q" using collinearorder[OF `axioms` `col A B Q`] by blast
			have "col B A R" using collinearorder[OF `axioms` `col A B R`] by blast
			have "col A R Q" using collinear4[OF `axioms` `col B A R` `col B A Q` `B \<noteq> A`] .
			have "col R F Q" using collinear4[OF `axioms` `col A R F` `col A R Q` `A \<noteq> R`] .
			have "col R Q F" using collinearorder[OF `axioms` `col R F Q`] by blast
		next
			case 2
			have "col R Q F" using collinear4[OF `axioms` `col B R Q` `col B R F` `B \<noteq> R`] .
		next
		have "col F Q R" using collinearorder[OF `axioms` `col R Q F`] by blast
		have "col C F Q" using col_b `axioms` `bet C F Q \<and> bet R F S` by blast
		have "col F Q C" using collinearorder[OF `axioms` `col C F Q`] by blast
		have "F \<noteq> Q" using betweennotequal[OF `axioms` `bet C F Q`] by blast
		have "col Q R C" using collinear4[OF `axioms` `col F Q R` `col F Q C` `F \<noteq> Q`] .
		have "col R Q C" using collinearorder[OF `axioms` `col Q R C`] by blast
		have "col R Q P" using col_b `axioms` `bet R Q P` by blast
		have "col Q R C" using collinearorder[OF `axioms` `col R Q C`] by blast
		have "col Q R P" using collinearorder[OF `axioms` `col R Q P`] by blast
		have "R \<noteq> Q" using betweennotequal[OF `axioms` `bet R Q P`] by blast
		have "Q \<noteq> R" using inequalitysymmetric[OF `axioms` `R \<noteq> Q`] .
		have "col R C P" using collinear4[OF `axioms` `col Q R C` `col Q R P` `Q \<noteq> R`] .
		have "col C P R" using collinearorder[OF `axioms` `col R C P`] by blast
		have "\<not> col C P R" using `\<not> col C P R` .
		show "False" using `\<not> col C P R` `col C P R` by blast
	qed
	hence "\<not> col A B Q" by blast
	have "bet Q F C" using betweennesssymmetryE[OF `axioms` `bet C F Q`] .
	have "bet Q F C \<and> col A B F \<and> \<not> col A B Q" using `bet Q F C` `col A B F` `\<not> col A B Q` by blast
	have "oppo_side Q A B C" sorry
	thus ?thesis by blast
qed

end