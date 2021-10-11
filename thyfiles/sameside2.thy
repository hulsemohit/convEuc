theory sameside2
	imports n3_6a n3_7a n9_5a n9_5b Geometry betweennotequal collinear4 collinearorder inequalitysymmetric ray1 rayimpliescollinear raystrict
begin

theorem(in euclidean_geometry) sameside2:
	assumes 
		"same_side E F A C"
		"col A B C"
		"ray_on B F G"
	shows "same_side E G A C"
proof -
	obtain Q U V where "col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F" using sameside_f[OF `same_side E F A C`]  by  blast
	have "col A C U" using `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
	have "col A C V" using `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
	have "bet E U Q" using `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
	have "bet F V Q" using `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
	have "\<not> col A C E" using `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
	have "\<not> col A C F" using `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
	have "oppo_side F A C Q" using oppositeside_b[OF `bet F V Q` `col A C V` `\<not> col A C F`] .
	have "col A C B" using collinearorder[OF `col A B C`] by blast
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> C)"
		hence "A = C" by blast
		have "col A C F" using collinear_b `A = C` by blast
		have "\<not> col A C F" using `\<not> col A C F` .
		show "False" using `\<not> col A C F` `col A C F` by blast
	qed
	hence "A \<noteq> C" by blast
	have "col B F G" using rayimpliescollinear[OF `ray_on B F G`] .
	have "col B G F" using collinearorder[OF `col B F G`] by blast
	have "col A C B" using collinearorder[OF `col A B C`] by blast
	have "\<not> (\<not> (oppo_side G A C Q))"
	proof (rule ccontr)
		assume "\<not> (\<not> (\<not> (oppo_side G A C Q)))"
hence "\<not> (oppo_side G A C Q)" by blast
		have "\<not> (F = G)"
		proof (rule ccontr)
			assume "\<not> (F \<noteq> G)"
			hence "F = G" by blast
			have "oppo_side G A C Q" using `oppo_side F A C Q` `F = G` by blast
			show "False" using `oppo_side G A C Q` `\<not> (oppo_side G A C Q)` by blast
		qed
		hence "F \<noteq> G" by blast
		have "\<not> (B = V)"
		proof (rule ccontr)
			assume "\<not> (B \<noteq> V)"
			hence "B = V" by blast
			have "bet F B Q" using `bet F V Q` `B = V` by blast
			have "bet B G F \<or> F = G \<or> bet B F G" using ray1[OF `ray_on B F G`] .
			consider "bet B G F"|"F = G"|"bet B F G" using `bet B G F \<or> F = G \<or> bet B F G`  by blast
			hence "bet G B Q"
			proof (cases)
				assume "bet B G F"
				have "bet F G B" using betweennesssymmetryE[OF `bet B G F`] .
				have "bet G B Q" using n3_6a[OF `bet F G B` `bet F B Q`] .
				thus ?thesis by blast
			next
				assume "F = G"
				have "\<not> (\<not> (bet G B Q))"
				proof (rule ccontr)
					assume "\<not> (\<not> (\<not> (bet G B Q)))"
hence "\<not> (bet G B Q)" by blast
					have "F \<noteq> G" using `F \<noteq> G` .
					show "False" using `F \<noteq> G` `F = G` by blast
				qed
				hence "bet G B Q" by blast
				thus ?thesis by blast
			next
				assume "bet B F G"
				have "bet G F B" using betweennesssymmetryE[OF `bet B F G`] .
				have "bet G B Q" using n3_7a[OF `bet G F B` `bet F B Q`] .
				thus ?thesis by blast
			qed
			have "\<not> (col A C G)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col A C G))"
hence "col A C G" by blast
				have "col A C B" using collinearorder[OF `col A B C`] by blast
				have "col C G B" using collinear4[OF `col A C G` `col A C B` `A \<noteq> C`] .
				have "col G B C" using collinearorder[OF `col C G B`] by blast
				have "col G B F" using collinearorder[OF `col B F G`] by blast
				have "B \<noteq> G" using raystrict[OF `ray_on B F G`] .
				have "G \<noteq> B" using inequalitysymmetric[OF `B \<noteq> G`] .
				have "col B C F" using collinear4[OF `col G B C` `col G B F` `G \<noteq> B`] .
				have "\<not> (B \<noteq> C)"
				proof (rule ccontr)
					assume "\<not> (\<not> (B \<noteq> C))"
hence "B \<noteq> C" by blast
					have "col B C A" using collinearorder[OF `col A B C`] by blast
					have "col C F A" using collinear4[OF `col B C F` `col B C A` `B \<noteq> C`] .
					have "col A C F" using collinearorder[OF `col C F A`] by blast
					show "False" using `col A C F` `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
				qed
				hence "B = C" by blast
				have "col A B G" using `col A C G` `B = C` by blast
				have "col G B A" using collinearorder[OF `col A B G`] by blast
				have "col G B F" using `col G B F` .
				have "col B A F" using collinear4[OF `col G B A` `col G B F` `G \<noteq> B`] .
				have "col A B F" using collinearorder[OF `col B A F`] by blast
				have "col A C F" using `col A B F` `B = C` by blast
				have "\<not> col A C F" using `\<not> col A C F` .
				show "False" using `\<not> col A C F` `col A C F` by blast
			qed
			hence "\<not> col A C G" by blast
			have "oppo_side G A C Q" using oppositeside_b[OF `bet G B Q` `col A C B` `\<not> col A C G`] .
			show "False" using `oppo_side G A C Q` `\<not> (oppo_side G A C Q)` by blast
		qed
		hence "B \<noteq> V" by blast
		have "\<not> (col Q F B)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col Q F B))"
hence "col Q F B" by blast
			have "col F V Q" using collinear_b `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
			have "col Q F V" using collinearorder[OF `col F V Q`] by blast
			have "F \<noteq> Q" using betweennotequal[OF `bet F V Q`] by blast
			have "Q \<noteq> F" using inequalitysymmetric[OF `F \<noteq> Q`] .
			have "col F B V" using collinear4[OF `col Q F B` `col Q F V` `Q \<noteq> F`] .
			have "A \<noteq> C" using `A \<noteq> C` .
			have "col C B V" using collinear4[OF `col A C B` `col A C V` `A \<noteq> C`] .
			have "col B V F" using collinearorder[OF `col F B V`] by blast
			have "col B V C" using collinearorder[OF `col C B V`] by blast
			have "col V F C" using collinear4[OF `col B V F` `col B V C` `B \<noteq> V`] .
			have "col V C F" using collinearorder[OF `col V F C`] by blast
			have "col V C A" using collinearorder[OF `col A C V`] by blast
			have "\<not> (V \<noteq> C)"
			proof (rule ccontr)
				assume "\<not> (\<not> (V \<noteq> C))"
hence "V \<noteq> C" by blast
				have "col C F A" using collinear4[OF `col V C F` `col V C A` `V \<noteq> C`] .
				have "col A C F" using collinearorder[OF `col C F A`] by blast
				have "\<not> col A C F" using `\<not> col A C F` .
				show "False" using `\<not> col A C F` `col A C F` by blast
			qed
			hence "V = C" by blast
			have "A \<noteq> C" using `A \<noteq> C` .
			have "A \<noteq> V" using `A \<noteq> C` `V = C` by blast
			have "V \<noteq> A" using inequalitysymmetric[OF `A \<noteq> V`] .
			have "col C A B" using collinearorder[OF `col A B C`] by blast
			have "col C A V" using collinearorder[OF `col A C V`] by blast
			have "C \<noteq> A" using inequalitysymmetric[OF `A \<noteq> C`] .
			have "col A B V" using collinear4[OF `col C A B` `col C A V` `C \<noteq> A`] .
			have "col B V A" using collinearorder[OF `col A B V`] by blast
			have "col V F A" using collinear4[OF `col B V F` `col B V A` `B \<noteq> V`] .
			have "col V A F" using collinearorder[OF `col V F A`] by blast
			have "col V A C" using collinearorder[OF `col A C V`] by blast
			have "col A F C" using collinear4[OF `col V A F` `col V A C` `V \<noteq> A`] .
			have "col A C F" using collinearorder[OF `col A F C`] by blast
			have "\<not> col A C F" using `\<not> col A C F` .
			show "False" using `\<not> col A C F` `col A C F` by blast
		qed
		hence "\<not> col Q F B" by blast
		have "bet B G F \<or> F = G \<or> bet B F G" using ray1[OF `ray_on B F G`] .
		consider "bet B G F"|"F = G"|"bet B F G" using `bet B G F \<or> F = G \<or> bet B F G`  by blast
		hence "oppo_side G A C Q"
		proof (cases)
			assume "bet B G F"
			have "oppo_side G A C Q" using n9_5b[OF `oppo_side F A C Q` `bet B G F` `\<not> col Q F B` `col A C B`] .
			thus ?thesis by blast
		next
			assume "F = G"
			have "oppo_side G A C Q" using `oppo_side F A C Q` `F = G` by blast
			thus ?thesis by blast
		next
			assume "bet B F G"
			have "\<not> (col B G Q)"
			proof (rule ccontr)
				assume "\<not> (\<not> (col B G Q))"
hence "col B G Q" by blast
				have "col G B F" using collinearorder[OF `col B F G`] by blast
				have "B \<noteq> G" using betweennotequal[OF `bet B F G`] by blast
				have "G \<noteq> B" using inequalitysymmetric[OF `B \<noteq> G`] .
				have "col G B Q" using collinearorder[OF `col B G Q`] by blast
				have "col B F Q" using collinear4[OF `col G B F` `col G B Q` `G \<noteq> B`] .
				have "col Q F B" using collinearorder[OF `col B F Q`] by blast
				have "\<not> col Q F B" using `\<not> col Q F B` .
				show "False" using `\<not> col Q F B` `col Q F B` by blast
			qed
			hence "\<not> col B G Q" by blast
			have "oppo_side G A C Q" using n9_5a[OF `oppo_side F A C Q` `bet B F G` `\<not> col B G Q` `col A C B`] .
			thus ?thesis by blast
		qed
		show "False" using `oppo_side G A C Q` `\<not> (oppo_side G A C Q)` by blast
	qed
	hence "oppo_side G A C Q" by blast
	obtain H where "bet G H Q \<and> col A C H \<and> \<not> col A C G" using oppositeside_f[OF `oppo_side G A C Q`]  by  blast
	have "\<not> col A C G" using `bet G H Q \<and> col A C H \<and> \<not> col A C G` by blast
	have "bet G H Q" using `bet G H Q \<and> col A C H \<and> \<not> col A C G` by blast
	have "col A C H" using `bet G H Q \<and> col A C H \<and> \<not> col A C G` by blast
	have "same_side E G A C" using sameside_b[OF `col A C U` `col A C H` `bet E U Q` `bet G H Q` `\<not> col A C E` `\<not> col A C G`] .
	thus ?thesis by blast
qed

end