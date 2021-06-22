theory sameside2
	imports Axioms Definitions Theorems
begin

theorem sameside2:
	assumes: `axioms`
		"same_side E F A C"
		"col A B C"
		"ray_on B F G"
	shows: "same_side E G A C"
proof -
	obtain Q U V where "col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F" sorry
	have "col A C U" using `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
	have "col A C V" using `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
	have "bet E U Q" using `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
	have "bet F V Q" using `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
	have "\<not> col A C E" using `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
	have "\<not> col A C F" using `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
	have "oppo_side F A C Q" sorry
	have "col A C B" using collinearorder[OF `axioms` `col A B C`] by blast
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "A = C"
		have "col A C F" using col_b `axioms` `A = C` by blast
		have "\<not> col A C F" using `\<not> col A C F` .
		show "False" using `\<not> col A C F` `col A C F` by blast
	qed
	hence "A \<noteq> C" by blast
	have "col B F G" using rayimpliescollinear[OF `axioms` `ray_on B F G`] .
	have "col B G F" using collinearorder[OF `axioms` `col B F G`] by blast
	have "col A C B" using collinearorder[OF `axioms` `col A B C`] by blast
	have "oppo_side G A C Q"
	proof (rule ccontr)
		assume "\<not> (oppo_side G A C Q)"
		have "\<not> (F = G)"
		proof (rule ccontr)
			assume "F = G"
			have "oppo_side G A C Q" sorry
			show "False" using `oppo_side G A C Q` `\<not> (oppo_side G A C Q)` by blast
		qed
		hence "F \<noteq> G" by blast
		have "\<not> (B = V)"
		proof (rule ccontr)
			assume "B = V"
			have "bet F B Q" sorry
			have "bet B G F \<or> F = G \<or> bet B F G" using ray1[OF `axioms` `ray_on B F G`] .
			consider "bet B G F"|"F = G"|"bet B F G" using `bet B G F \<or> F = G \<or> bet B F G`  by blast
			hence bet G B Q
			proof (cases)
				case 1
				have "bet F G B" using betweennesssymmetryE[OF `axioms` `bet B G F`] .
				have "bet G B Q" using n3_6a[OF `axioms` `bet F G B` `bet F B Q`] .
			next
				case 2
				have "bet G B Q"
				proof (rule ccontr)
					assume "\<not> (bet G B Q)"
					have "F \<noteq> G" using `F \<noteq> G` .
					show "False" using `F \<noteq> G` `F = G` by blast
				qed
				hence "bet G B Q" by blast
			next
				case 3
				have "bet G F B" using betweennesssymmetryE[OF `axioms` `bet B F G`] .
				have "bet G B Q" using n3_7a[OF `axioms` `bet G F B` `bet F B Q`] .
			next
			have "\<not> (col A C G)"
			proof (rule ccontr)
				assume "col A C G"
				have "col A C B" using collinearorder[OF `axioms` `col A B C`] by blast
				have "col C G B" using collinear4[OF `axioms` `col A C G` `col A C B` `A \<noteq> C`] .
				have "col G B C" using collinearorder[OF `axioms` `col C G B`] by blast
				have "col G B F" using collinearorder[OF `axioms` `col B F G`] by blast
				have "B \<noteq> G" using raystrict[OF `axioms` `ray_on B F G`] .
				have "G \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> G`] .
				have "col B C F" using collinear4[OF `axioms` `col G B C` `col G B F` `G \<noteq> B`] .
				have "\<not> (B \<noteq> C)"
				proof (rule ccontr)
					assume "B \<noteq> C"
					have "col B C A" using collinearorder[OF `axioms` `col A B C`] by blast
					have "col C F A" using collinear4[OF `axioms` `col B C F` `col B C A` `B \<noteq> C`] .
					have "col A C F" using collinearorder[OF `axioms` `col C F A`] by blast
					show "False" using `col A C F` `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
				qed
				hence "B = C" by blast
				have "col A B G" sorry
				have "col G B A" using collinearorder[OF `axioms` `col A B G`] by blast
				have "col G B F" using `col G B F` .
				have "col B A F" using collinear4[OF `axioms` `col G B A` `col G B F` `G \<noteq> B`] .
				have "col A B F" using collinearorder[OF `axioms` `col B A F`] by blast
				have "col A C F" sorry
				have "\<not> col A C F" using `\<not> col A C F` .
				show "False" using `\<not> col A C F` `col A C F` by blast
			qed
			hence "\<not> col A C G" by blast
			have "oppo_side G A C Q" sorry
			show "False" using `oppo_side G A C Q` `\<not> (oppo_side G A C Q)` by blast
		qed
		hence "B \<noteq> V" by blast
		have "\<not> (col Q F B)"
		proof (rule ccontr)
			assume "col Q F B"
			have "col F V Q" using col_b `axioms` `col A C U \<and> col A C V \<and> bet E U Q \<and> bet F V Q \<and> \<not> col A C E \<and> \<not> col A C F` by blast
			have "col Q F V" using collinearorder[OF `axioms` `col F V Q`] by blast
			have "F \<noteq> Q" using betweennotequal[OF `axioms` `bet F V Q`] by blast
			have "Q \<noteq> F" using inequalitysymmetric[OF `axioms` `F \<noteq> Q`] .
			have "col F B V" using collinear4[OF `axioms` `col Q F B` `col Q F V` `Q \<noteq> F`] .
			have "A \<noteq> C" using `A \<noteq> C` .
			have "col C B V" using collinear4[OF `axioms` `col A C B` `col A C V` `A \<noteq> C`] .
			have "col B V F" using collinearorder[OF `axioms` `col F B V`] by blast
			have "col B V C" using collinearorder[OF `axioms` `col C B V`] by blast
			have "col V F C" using collinear4[OF `axioms` `col B V F` `col B V C` `B \<noteq> V`] .
			have "col V C F" using collinearorder[OF `axioms` `col V F C`] by blast
			have "col V C A" using collinearorder[OF `axioms` `col A C V`] by blast
			have "\<not> (V \<noteq> C)"
			proof (rule ccontr)
				assume "V \<noteq> C"
				have "col C F A" using collinear4[OF `axioms` `col V C F` `col V C A` `V \<noteq> C`] .
				have "col A C F" using collinearorder[OF `axioms` `col C F A`] by blast
				have "\<not> col A C F" using `\<not> col A C F` .
				show "False" using `\<not> col A C F` `col A C F` by blast
			qed
			hence "V = C" by blast
			have "A \<noteq> C" using `A \<noteq> C` .
			have "A \<noteq> V" sorry
			have "V \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> V`] .
			have "col C A B" using collinearorder[OF `axioms` `col A B C`] by blast
			have "col C A V" using collinearorder[OF `axioms` `col A C V`] by blast
			have "C \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> C`] .
			have "col A B V" using collinear4[OF `axioms` `col C A B` `col C A V` `C \<noteq> A`] .
			have "col B V A" using collinearorder[OF `axioms` `col A B V`] by blast
			have "col V F A" using collinear4[OF `axioms` `col B V F` `col B V A` `B \<noteq> V`] .
			have "col V A F" using collinearorder[OF `axioms` `col V F A`] by blast
			have "col V A C" using collinearorder[OF `axioms` `col A C V`] by blast
			have "col A F C" using collinear4[OF `axioms` `col V A F` `col V A C` `V \<noteq> A`] .
			have "col A C F" using collinearorder[OF `axioms` `col A F C`] by blast
			have "\<not> col A C F" using `\<not> col A C F` .
			show "False" using `\<not> col A C F` `col A C F` by blast
		qed
		hence "\<not> col Q F B" by blast
		have "bet B G F \<or> F = G \<or> bet B F G" using ray1[OF `axioms` `ray_on B F G`] .
		consider "bet B G F"|"F = G"|"bet B F G" using `bet B G F \<or> F = G \<or> bet B F G`  by blast
		hence oppo_side G A C Q
		proof (cases)
			case 1
			have "oppo_side G A C Q" using n9_5b[OF `axioms` `oppo_side F A C Q` `bet B G F` `\<not> col Q F B` `col A C B`] .
		next
			case 2
			have "oppo_side G A C Q" sorry
		next
			case 3
			have "\<not> (col B G Q)"
			proof (rule ccontr)
				assume "col B G Q"
				have "col G B F" using collinearorder[OF `axioms` `col B F G`] by blast
				have "B \<noteq> G" using betweennotequal[OF `axioms` `bet B F G`] by blast
				have "G \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> G`] .
				have "col G B Q" using collinearorder[OF `axioms` `col B G Q`] by blast
				have "col B F Q" using collinear4[OF `axioms` `col G B F` `col G B Q` `G \<noteq> B`] .
				have "col Q F B" using collinearorder[OF `axioms` `col B F Q`] by blast
				have "\<not> col Q F B" using `\<not> col Q F B` .
				show "False" using `\<not> col Q F B` `col Q F B` by blast
			qed
			hence "\<not> col B G Q" by blast
			have "oppo_side G A C Q" using n9_5a[OF `axioms` `oppo_side F A C Q` `bet B F G` `\<not> col B G Q` `col A C B`] .
		next
		show "False" using `oppo_side G A C Q` `\<not> (oppo_side G A C Q)` by blast
	qed
	hence "oppo_side G A C Q" by blast
	obtain H where "bet G H Q \<and> col A C H \<and> \<not> col A C G" sorry
	have "\<not> col A C G" using `bet G H Q \<and> col A C H \<and> \<not> col A C G` by blast
	have "bet G H Q" using `bet G H Q \<and> col A C H \<and> \<not> col A C G` by blast
	have "col A C H" using `bet G H Q \<and> col A C H \<and> \<not> col A C G` by blast
	have "same_side E G A C" sorry
	thus ?thesis by blast
qed

end