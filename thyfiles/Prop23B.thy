theory Prop23B
	imports Axioms Definitions Theorems
begin

theorem Prop23B:
	assumes: `axioms`
		"A \<noteq> B"
		"\<not> col D C E"
		"\<not> col A B P"
	shows: "\<exists> G S. ray_on A B G \<and> ang_eq S A G D C E \<and> oppo_side S A B P"
proof -
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	obtain F G where "ray_on A B G \<and> ang_eq F A G D C E" using Prop23[OF `axioms` `A \<noteq> B` `\<not> col D C E`]  by  blast
	have "ray_on A B G" using `ray_on A B G \<and> ang_eq F A G D C E` by blast
	have "A \<noteq> G" using raystrict[OF `axioms` `ray_on A B G`] .
	have "ang_eq F A G D C E" using `ray_on A B G \<and> ang_eq F A G D C E` by blast
	have "\<not> (col A B F)"
	proof (rule ccontr)
		assume "col A B F"
		have "ang_eq D C E F A G" using equalanglessymmetric[OF `axioms` `ang_eq F A G D C E`] .
		have "\<not> col F A G" using equalanglesNC[OF `axioms` `ang_eq D C E F A G`] .
		have "col A B G" using rayimpliescollinear[OF `axioms` `ray_on A B G`] .
		have "col B F G" using collinear4[OF `axioms` `col A B F` `col A B G` `A \<noteq> B`] .
		have "col B F A" using collinearorder[OF `axioms` `col A B F`] by blast
		have "\<not> (F = B)"
		proof (rule ccontr)
			assume "F = B"
			have "ray_on A F G" sorry
			have "col A F G" using rayimpliescollinear[OF `axioms` `ray_on A F G`] .
			have "col F A G" using collinearorder[OF `axioms` `col A F G`] by blast
			show "False" using `col F A G` `\<not> col F A G` by blast
		qed
		hence "F \<noteq> B" by blast
		have "B \<noteq> F" using inequalitysymmetric[OF `axioms` `F \<noteq> B`] .
		have "col F A G" using collinear4[OF `axioms` `col B F A` `col B F G` `B \<noteq> F`] .
		show "False" using `col F A G` `\<not> col F A G` by blast
	qed
	hence "\<not> col A B F" by blast
	obtain H where "perp_at F H A B H" using Prop12[OF `axioms` `A \<noteq> B` `\<not> col A B F`]  by  blast
	obtain J where "col F H H \<and> col A B H \<and> col A B J \<and> ang_right J H F" sorry
	have "col A B H" using `col F H H \<and> col A B H \<and> col A B J \<and> ang_right J H F` by blast
	have "ang_right J H F" using `col F H H \<and> col A B H \<and> col A B J \<and> ang_right J H F` by blast
	have "\<not> col J H F" using rightangleNC[OF `axioms` `ang_right J H F`] .
	have "\<not> (F = H)"
	proof (rule ccontr)
		assume "F = H"
		have "col A B F" sorry
		have "\<not> col A B F" using `\<not> col A B F` .
		show "False" using `\<not> col A B F` `col A B F` by blast
	qed
	hence "F \<noteq> H" by blast
	have "\<not> (J = H)"
	proof (rule ccontr)
		assume "J = H"
		have "col J H F" using col_b `axioms` `J = H` by blast
		show "False" using `col J H F` `\<not> col J H F` by blast
	qed
	hence "J \<noteq> H" by blast
	have "H \<noteq> J" using inequalitysymmetric[OF `axioms` `J \<noteq> H`] .
	obtain T where "bet J H T \<and> seg_eq H T H J" using extensionE[OF `axioms` `J \<noteq> H` `H \<noteq> J`]  by  blast
	have "bet J H T" using `bet J H T \<and> seg_eq H T H J` by blast
	have "col J H T" using col_b `axioms` `bet J H T \<and> seg_eq H T H J` by blast
	have "col A B J" using `col F H H \<and> col A B H \<and> col A B J \<and> ang_right J H F` by blast
	have "col A B H" using `col A B H` .
	have "col B J H" using collinear4[OF `axioms` `col A B J` `col A B H` `A \<noteq> B`] .
	have "J \<noteq> T" using betweennotequal[OF `axioms` `bet J H T`] by blast
	have "col H J B" using collinearorder[OF `axioms` `col B J H`] by blast
	have "col H J T" using collinearorder[OF `axioms` `col J H T`] by blast
	have "J \<noteq> H" using betweennotequal[OF `axioms` `bet J H T`] by blast
	have "H \<noteq> J" using inequalitysymmetric[OF `axioms` `J \<noteq> H`] .
	have "col J B T" using collinear4[OF `axioms` `col H J B` `col H J T` `H \<noteq> J`] .
	have "col J T B" using collinearorder[OF `axioms` `col J B T`] by blast
	have "col B A J" using collinearorder[OF `axioms` `col A B J`] by blast
	have "col B A H" using collinearorder[OF `axioms` `col A B H`] by blast
	have "col A J H" using collinear4[OF `axioms` `col B A J` `col B A H` `B \<noteq> A`] .
	have "col H J A" using collinearorder[OF `axioms` `col A J H`] by blast
	have "col J A T" using collinear4[OF `axioms` `col H J A` `col H J T` `H \<noteq> J`] .
	have "col J T A" using collinearorder[OF `axioms` `col J A T`] by blast
	have "\<not> (col J T P)"
	proof (rule ccontr)
		assume "col J T P"
		have "col J T P" using `col J T P` .
		have "col A B P" using collinear5[OF `axioms` `J \<noteq> T` `col J T A` `col J T B` `col J T P`] .
		show "False" using `col A B P` `\<not> col A B P` by blast
	qed
	hence "\<not> col J T P" by blast
	obtain Q where "ang_right J H Q \<and> oppo_side Q J T P" using Prop11B[OF `axioms` `bet J H T` `\<not> col J T P`]  by  blast
	have "ang_right J H Q" using `ang_right J H Q \<and> oppo_side Q J T P` by blast
	have "\<not> col J H Q" using rightangleNC[OF `axioms` `ang_right J H Q`] .
	have "\<not> (H = Q)"
	proof (rule ccontr)
		assume "H = Q"
		have "col J H Q" using col_b `axioms` `H = Q` by blast
		show "False" using `col J H Q` `\<not> col J H Q` by blast
	qed
	hence "H \<noteq> Q" by blast
	have "\<not> (H = F)"
	proof (rule ccontr)
		assume "H = F"
		have "col J H F" using col_b `axioms` `H = F` by blast
		show "False" using `col J H F` `\<not> col J H F` by blast
	qed
	hence "H \<noteq> F" by blast
	obtain S where "ray_on H Q S \<and> seg_eq H S H F" using layoff[OF `axioms` `H \<noteq> Q` `H \<noteq> F`]  by  blast
	have "ray_on H Q S" using `ray_on H Q S \<and> seg_eq H S H F` by blast
	have "seg_eq H S H F" using `ray_on H Q S \<and> seg_eq H S H F` by blast
	have "F = F" using equalityreflexiveE[OF `axioms`] .
	have "D \<noteq> C" using angledistinct[OF `axioms` `ang_eq F A G D C E`] by blast
	have "C \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> C`] .
	have "C \<noteq> E" using angledistinct[OF `axioms` `ang_eq F A G D C E`] by blast
	have "ang_right J H F" using `ang_right J H F` .
	have "col J H A" using collinearorder[OF `axioms` `col A J H`] by blast
	have "ang_right J H Q" using `ang_right J H Q` .
	have "ang_right J H S" using n8_3[OF `axioms` `ang_right J H Q` `ray_on H Q S`] .
	have "ang_right S H J" using n8_2[OF `axioms` `ang_right J H S`] .
	have "ang_eq J H F J H S" using Euclid4[OF `axioms` `ang_right J H F` `ang_right J H S`] .
	have "S = S" using equalityreflexiveE[OF `axioms`] .
	have "H \<noteq> S" using angledistinct[OF `axioms` `ang_eq J H F J H S`] by blast
	consider "A = H"|"A \<noteq> H" by blast
	hence ang_eq F A G S A G
	proof (cases)
		case 1
		have "A \<noteq> G" using `A \<noteq> G` .
		have "ang_right J A F" sorry
		have "ang_right J A S" sorry
		have "col A B H" using `col A B H` .
		have "col A B J" using `col A B J` .
		have "col A B G" using rayimpliescollinear[OF `axioms` `ray_on A B G`] .
		have "col J H G" using collinear5[OF `axioms` `A \<noteq> B` `col A B J` `col A B H` `col A B G`] .
		have "col J A G" sorry
		have "ang_right J A F" using `ang_right J A F` .
		have "G \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> G`] .
		have "ang_right G A F" using collinearright[OF `axioms` `ang_right J A F` `col J A G` `G \<noteq> A`] .
		have "ang_right F A G" using n8_2[OF `axioms` `ang_right G A F`] .
		have "ang_right J A S" using `ang_right J A S` .
		have "ang_right G A S" using collinearright[OF `axioms` `ang_right J A S` `col J A G` `G \<noteq> A`] .
		have "ang_right S A G" using n8_2[OF `axioms` `ang_right G A S`] .
		have "ang_eq F A G S A G" using Euclid4[OF `axioms` `ang_right F A G` `ang_right S A G`] .
	next
		case 2
		have "seg_eq F H S H" using doublereverse[OF `axioms` `seg_eq H S H F`] by blast
		have "ang_right J H F" using `ang_right J H F` .
		have "ang_right A H F" using collinearright[OF `axioms` `ang_right J H F` `col J H A` `A \<noteq> H`] .
		have "ang_right F H A" using n8_2[OF `axioms` `ang_right A H F`] .
		have "ang_right S H J" using `ang_right S H J` .
		have "ang_right J H S" using n8_2[OF `axioms` `ang_right S H J`] .
		have "ang_right A H S" using collinearright[OF `axioms` `ang_right J H S` `col J H A` `A \<noteq> H`] .
		have "ang_eq A H F A H S" using Euclid4[OF `axioms` `ang_right A H F` `ang_right A H S`] .
		have "\<not> col F H A" using rightangleNC[OF `axioms` `ang_right F H A`] .
		have "ang_eq F H A A H F" using ABCequalsCBA[OF `axioms` `\<not> col F H A`] .
		have "ang_eq F H A A H S" using equalanglestransitive[OF `axioms` `ang_eq F H A A H F` `ang_eq A H F A H S`] .
		have "\<not> col A H S" using rightangleNC[OF `axioms` `ang_right A H S`] .
		have "ang_eq A H S S H A" using ABCequalsCBA[OF `axioms` `\<not> col A H S`] .
		have "ang_eq F H A S H A" using equalanglestransitive[OF `axioms` `ang_eq F H A A H S` `ang_eq A H S S H A`] .
		have "seg_eq H F H S" using congruenceflip[OF `axioms` `seg_eq F H S H`] by blast
		have "seg_eq H A H A" using congruencereflexiveE[OF `axioms`] .
		have "\<not> (col S H A)"
		proof (rule ccontr)
			assume "col S H A"
			have "col A H S" using collinearorder[OF `axioms` `col S H A`] by blast
			show "False" using `col A H S` `\<not> col A H S` by blast
		qed
		hence "\<not> col S H A" by blast
		have "seg_eq F A S A \<and> ang_eq H F A H S A \<and> ang_eq H A F H A S" using Prop04[OF `axioms` `seg_eq H F H S` `seg_eq H A H A` `ang_eq F H A S H A`] .
		have "ang_eq H A F H A S" using `seg_eq F A S A \<and> ang_eq H F A H S A \<and> ang_eq H A F H A S` by blast
		have "\<not> (col F A H)"
		proof (rule ccontr)
			assume "col F A H"
			have "col F H A" using collinearorder[OF `axioms` `col F A H`] by blast
			show "False" using `col F H A` `\<not> col F H A` by blast
		qed
		hence "\<not> col F A H" by blast
		have "ang_eq F A H H A F" using ABCequalsCBA[OF `axioms` `\<not> col F A H`] .
		have "\<not> (col H A S)"
		proof (rule ccontr)
			assume "col H A S"
			have "col S H A" using collinearorder[OF `axioms` `col H A S`] by blast
			show "False" using `col S H A` `\<not> col S H A` by blast
		qed
		hence "\<not> col H A S" by blast
		have "ang_eq H A S S A H" using ABCequalsCBA[OF `axioms` `\<not> col H A S`] .
		have "ang_eq F A H H A S" using equalanglestransitive[OF `axioms` `ang_eq F A H H A F` `ang_eq H A F H A S`] .
		have "ang_eq F A H S A H" using equalanglestransitive[OF `axioms` `ang_eq F A H H A S` `ang_eq H A S S A H`] .
		have "ray_on A B G" using `ray_on A B G` .
		have "col A B H" using `col A B H` .
		have "A = A" using equalityreflexiveE[OF `axioms`] .
		have "col A B A" using col_b `axioms` `A = A` by blast
		have "col A B G" using rayimpliescollinear[OF `axioms` `ray_on A B G`] .
		consider "G = H"|"G \<noteq> H" by blast
		hence col G H A
		proof (cases)
			case 1
			have "col G H A" using col_b `axioms` `G = H` by blast
		next
			case 2
			have "col G H A" using collinear5[OF `axioms` `A \<noteq> B` `col A B G` `col A B H` `col A B A`] .
		next
		have "F \<noteq> A" using angledistinct[OF `axioms` `ang_eq F A G D C E`] by blast
		have "A \<noteq> F" using inequalitysymmetric[OF `axioms` `F \<noteq> A`] .
		have "ray_on A F F" using ray4 `axioms` `F = F` `A \<noteq> F` by blast
		have "S \<noteq> A" using angledistinct[OF `axioms` `ang_eq A H S S H A`] by blast
		have "A \<noteq> S" using inequalitysymmetric[OF `axioms` `S \<noteq> A`] .
		have "ray_on A S S" using ray4 `axioms` `S = S` `A \<noteq> S` by blast
		have "G = H \<or> G = A \<or> H = A \<or> bet H G A \<or> bet G H A \<or> bet G A H" using col_f[OF `axioms` `col G H A`] .
		consider "G = H"|"G = A"|"H = A"|"bet H G A"|"bet G H A"|"bet G A H" using `G = H \<or> G = A \<or> H = A \<or> bet H G A \<or> bet G H A \<or> bet G A H`  by blast
		hence ang_eq F A G S A G
		proof (cases)
			case 1
			have "ang_eq F A G S A G"
			proof (rule ccontr)
				assume "\<not> (ang_eq F A G S A G)"
				have "ang_eq F A G S A G" sorry
				show "False" using `ang_eq F A G S A G` `\<not> (ang_eq F A G S A G)` by blast
			qed
			hence "ang_eq F A G S A G" by blast
		next
			case 2
			have "ang_eq F A G S A G"
			proof (rule ccontr)
				assume "\<not> (ang_eq F A G S A G)"
				have "ray_on A B G" using `ray_on A B G` .
				have "A \<noteq> G" using raystrict[OF `axioms` `ray_on A B G`] .
				have "G \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> G`] .
				show "False" using `G \<noteq> A` `G = A` by blast
			qed
			hence "ang_eq F A G S A G" by blast
		next
			case 3
			have "ang_eq F A G S A G"
			proof (rule ccontr)
				assume "\<not> (ang_eq F A G S A G)"
				have "H \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> H`] .
				show "False" using `H \<noteq> A` `H = A` by blast
			qed
			hence "ang_eq F A G S A G" by blast
		next
			case 4
			have "bet A G H" using betweennesssymmetryE[OF `axioms` `bet H G A`] .
			have "ray_on A H G" using ray4 `axioms` `bet A G H` `A \<noteq> H` by blast
			have "ang_eq F A H F A H" using equalanglesreflexive[OF `axioms` `\<not> col F A H`] .
			have "\<not> (col S A H)"
			proof (rule ccontr)
				assume "col S A H"
				have "col S H A" using collinearorder[OF `axioms` `col S A H`] by blast
				show "False" using `col S H A` `\<not> col S H A` by blast
			qed
			hence "\<not> col S A H" by blast
			have "ang_eq S A H S A H" using equalanglesreflexive[OF `axioms` `\<not> col S A H`] .
			have "ang_eq F A H F A G" using equalangleshelper[OF `axioms` `ang_eq F A H F A H` `ray_on A F F` `ray_on A H G`] .
			have "ang_eq S A H S A G" using equalangleshelper[OF `axioms` `ang_eq S A H S A H` `ray_on A S S` `ray_on A H G`] .
			have "ang_eq F A G F A H" using equalanglessymmetric[OF `axioms` `ang_eq F A H F A G`] .
			have "ang_eq F A G S A H" using equalanglestransitive[OF `axioms` `ang_eq F A G F A H` `ang_eq F A H S A H`] .
			have "ang_eq F A G S A G" using equalanglestransitive[OF `axioms` `ang_eq F A G S A H` `ang_eq S A H S A G`] .
		next
			case 5
			have "bet A H G" using betweennesssymmetryE[OF `axioms` `bet G H A`] .
			have "ray_on A H G" using ray4 `axioms` `bet A H G` `A \<noteq> H` by blast
			have "ang_eq F A H F A H" using equalanglesreflexive[OF `axioms` `\<not> col F A H`] .
			have "\<not> (col S A H)"
			proof (rule ccontr)
				assume "col S A H"
				have "col S H A" using collinearorder[OF `axioms` `col S A H`] by blast
				show "False" using `col S H A` `\<not> col S H A` by blast
			qed
			hence "\<not> col S A H" by blast
			have "ang_eq S A H S A H" using equalanglesreflexive[OF `axioms` `\<not> col S A H`] .
			have "ang_eq F A H F A G" using equalangleshelper[OF `axioms` `ang_eq F A H F A H` `ray_on A F F` `ray_on A H G`] .
			have "ang_eq S A H S A G" using equalangleshelper[OF `axioms` `ang_eq S A H S A H` `ray_on A S S` `ray_on A H G`] .
			have "ang_eq F A G F A H" using equalanglessymmetric[OF `axioms` `ang_eq F A H F A G`] .
			have "ang_eq F A G S A H" using equalanglestransitive[OF `axioms` `ang_eq F A G F A H` `ang_eq F A H S A H`] .
			have "ang_eq F A G S A G" using equalanglestransitive[OF `axioms` `ang_eq F A G S A H` `ang_eq S A H S A G`] .
		next
			case 6
			have "bet H A G" using betweennesssymmetryE[OF `axioms` `bet G A H`] .
			have "ray_on A F F" using `ray_on A F F` .
			have "linear_pair H A F F G" sorry
			have "linear_pair H A S S G" sorry
			have "ang_eq F A H S A H" using `ang_eq F A H S A H` .
			have "ang_eq H A F H A S" using equalanglesflip[OF `axioms` `ang_eq F A H S A H`] .
			have "ang_eq F A G S A G" using supplements[OF `axioms` `ang_eq H A F H A S` `linear_pair H A F F G` `linear_pair H A S S G`] .
		next
	next
	have "ang_eq S A G F A G" using equalanglessymmetric[OF `axioms` `ang_eq F A G S A G`] .
	have "ang_eq F A G D C E" using `ang_eq F A G D C E` .
	have "ang_eq S A G D C E" using equalanglestransitive[OF `axioms` `ang_eq S A G F A G` `ang_eq F A G D C E`] .
	have "oppo_side Q J T P" using `ang_right J H Q \<and> oppo_side Q J T P` by blast
	have "ray_on H Q S" using `ray_on H Q S` .
	have "ray_on H S Q" using ray5[OF `axioms` `ray_on H Q S`] .
	have "col J T H" using collinearorder[OF `axioms` `col H J T`] by blast
	have "oppo_side S J T P" using n9_5[OF `axioms` `oppo_side Q J T P` `ray_on H S Q` `col J T H`] .
	obtain M where "bet S M P \<and> col J T M \<and> \<not> col J T S" sorry
	have "bet S M P" using `bet S M P \<and> col J T M \<and> \<not> col J T S` by blast
	have "col J T M" using `bet S M P \<and> col J T M \<and> \<not> col J T S` by blast
	have "\<not> col J T S" using `bet S M P \<and> col J T M \<and> \<not> col J T S` by blast
	have "col A B J" using `col A B J` .
	have "col J T A" using `col J T A` .
	have "col J T B" using `col J T B` .
	have "J \<noteq> T" using `J \<noteq> T` .
	have "col T A B" using collinear4[OF `axioms` `col J T A` `col J T B` `J \<noteq> T`] .
	have "col A B T" using collinearorder[OF `axioms` `col T A B`] by blast
	have "col B A T" using collinearorder[OF `axioms` `col A B T`] by blast
	have "col A J T" using collinear4[OF `axioms` `col B A J` `col B A T` `B \<noteq> A`] .
	have "col J T A" using collinearorder[OF `axioms` `col A J T`] by blast
	have "col B J T" using collinear4[OF `axioms` `col A B J` `col A B T` `A \<noteq> B`] .
	have "col J T B" using collinearorder[OF `axioms` `col B J T`] by blast
	have "J \<noteq> T" using `J \<noteq> T` .
	have "col A B M" using collinear5[OF `axioms` `J \<noteq> T` `col J T A` `col J T B` `col J T M`] .
	have "\<not> (col A B S)"
	proof (rule ccontr)
		assume "col A B S"
		have "col A B J" using `col A B J` .
		have "col A B T" using `col A B T` .
		have "col J T S" using collinear5[OF `axioms` `A \<noteq> B` `col A B J` `col A B T` `col A B S`] .
		show "False" using `col J T S` `bet S M P \<and> col J T M \<and> \<not> col J T S` by blast
	qed
	hence "\<not> col A B S" by blast
	have "oppo_side S A B P" sorry
	have "ray_on A B G \<and> ang_eq S A G D C E \<and> oppo_side S A B P" using `ray_on A B G \<and> ang_eq F A G D C E` `ang_eq S A G D C E` `oppo_side S A B P` by blast
	thus ?thesis by blast
qed

end