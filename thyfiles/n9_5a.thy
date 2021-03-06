theory n9_5a
	imports Geometry betweennotequal collinear4 collinearorder inequalitysymmetric
begin

theorem(in euclidean_geometry) n9_5a:
	assumes 
		"oppo_side P A B C"
		"bet R P Q"
		"\<not> col R Q C"
		"col A B R"
	shows "oppo_side Q A B C"
proof -
	obtain S where "bet P S C \<and> col A B S \<and> \<not> col A B P" using oppositeside_f[OF `oppo_side P A B C`]  by  blast
	have "bet P S C" using `bet P S C \<and> col A B S \<and> \<not> col A B P` by blast
	have "\<not> col A B P" using `bet P S C \<and> col A B S \<and> \<not> col A B P` by blast
	have "bet C S P" using betweennesssymmetryE[OF `bet P S C`] .
	obtain F where "bet C F Q \<and> bet R S F" using Pasch_outerE[OF `bet C S P` `bet R P Q` `\<not> col R Q C`]  by  blast
	have "bet C F Q" using `bet C F Q \<and> bet R S F` by blast
	have "bet R S F" using `bet C F Q \<and> bet R S F` by blast
	have "col R S F" using collinear_b `bet C F Q \<and> bet R S F` by blast
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> B)"
		hence "A = B" by blast
		have "col A B P" using collinear_b `A = B` by blast
		show "False" using `col A B P` `bet P S C \<and> col A B S \<and> \<not> col A B P` by blast
	qed
	hence "A \<noteq> B" by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	have "col A B R" using `col A B R` .
	have "col A B S" using `bet P S C \<and> col A B S \<and> \<not> col A B P` by blast
	have "col B R S" using collinear4[OF `col A B R` `col A B S` `A \<noteq> B`] .
	have "col R S B" using collinearorder[OF `col B R S`] by blast
	have "R \<noteq> S" using betweennotequal[OF `bet R S F`] by blast
	have "col S F B" using collinear4[OF `col R S F` `col R S B` `R \<noteq> S`] .
	have "col S B A" using collinearorder[OF `col A B S`] by blast
	have "col S B F" using collinearorder[OF `col S F B`] by blast
	consider "S = B"|"S \<noteq> B" by blast
	hence "col A B F"
	proof (cases)
		assume "S = B"
		have "col R S F" using collinear_b `bet C F Q \<and> bet R S F` by blast
		have "col R B F" using `col R S F` `S = B` by blast
		have "col R B A" using collinearorder[OF `col A B R`] by blast
		have "\<not> (R = B)"
		proof (rule ccontr)
			assume "\<not> (R \<noteq> B)"
			hence "R = B" by blast
			have "bet R S F" using `bet R S F` .
			have "R \<noteq> S" using betweennotequal[OF `bet R S F`] by blast
			have "R \<noteq> B" using `R \<noteq> S` `S = B` by blast
			show "False" using `R \<noteq> B` `R = B` by blast
		qed
		hence "R \<noteq> B" by blast
		have "col B F A" using collinear4[OF `col R B F` `col R B A` `R \<noteq> B`] .
		have "col A B F" using collinearorder[OF `col B F A`] by blast
		thus ?thesis by blast
	next
		assume "S \<noteq> B"
		have "col B A F" using collinear4[OF `col S B A` `col S B F` `S \<noteq> B`] .
		have "col A B F" using collinearorder[OF `col B A F`] by blast
		thus ?thesis by blast
	qed
	have "\<not> (col A B Q)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A B Q))"
hence "col A B Q" by blast
		have "col A B R" using `col A B R` .
		have "col B Q R" using collinear4[OF `col A B Q` `col A B R` `A \<noteq> B`] .
		have "col B R Q" using collinearorder[OF `col B Q R`] by blast
		have "col A B R" using `col A B R` .
		have "col A B F" using `col A B F` .
		have "col B R F" using collinear4[OF `col A B R` `col A B F` `A \<noteq> B`] .
		consider "B = R"|"B \<noteq> R" by blast
		hence "col R Q F"
		proof (cases)
			assume "B = R"
			have "\<not> (A = R)"
			proof (rule ccontr)
				assume "\<not> (A \<noteq> R)"
				hence "A = R" by blast
				have "A = B" using `A = R` `B = R` by blast
				show "False" using `A = B` `A \<noteq> B` by blast
			qed
			hence "A \<noteq> R" by blast
			have "col B A R" using collinearorder[OF `col A B R`] by blast
			have "col B A F" using collinearorder[OF `col A B F`] by blast
			have "col A R F" using collinear4[OF `col B A R` `col B A F` `B \<noteq> A`] .
			have "col B A Q" using collinearorder[OF `col A B Q`] by blast
			have "col B A R" using collinearorder[OF `col A B R`] by blast
			have "col A R Q" using collinear4[OF `col B A R` `col B A Q` `B \<noteq> A`] .
			have "col R F Q" using collinear4[OF `col A R F` `col A R Q` `A \<noteq> R`] .
			have "col R Q F" using collinearorder[OF `col R F Q`] by blast
			thus ?thesis by blast
		next
			assume "B \<noteq> R"
			have "col R Q F" using collinear4[OF `col B R Q` `col B R F` `B \<noteq> R`] .
			thus ?thesis by blast
		qed
		have "col F Q R" using collinearorder[OF `col R Q F`] by blast
		have "col C F Q" using collinear_b `bet C F Q \<and> bet R S F` by blast
		have "col F Q C" using collinearorder[OF `col C F Q`] by blast
		have "F \<noteq> Q" using betweennotequal[OF `bet C F Q`] by blast
		have "col Q R C" using collinear4[OF `col F Q R` `col F Q C` `F \<noteq> Q`] .
		have "col R Q C" using collinearorder[OF `col Q R C`] by blast
		have "\<not> col R Q C" using `\<not> col R Q C` .
		show "False" using `\<not> col R Q C` `col R Q C` by blast
	qed
	hence "\<not> col A B Q" by blast
	have "bet Q F C" using betweennesssymmetryE[OF `bet C F Q`] .
	have "bet Q F C \<and> col A B F \<and> \<not> col A B Q" using `bet Q F C` `col A B F` `\<not> col A B Q` by blast
	have "oppo_side Q A B C" using oppositeside_b[OF `bet Q F C` `col A B F` `\<not> col A B Q`] .
	thus ?thesis by blast
qed

end