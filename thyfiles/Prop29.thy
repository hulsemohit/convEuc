theory Prop29
	imports Axioms Definitions Theorems
begin

theorem Prop29:
	assumes: `axioms`
		"parallel A B C D"
		"bet A G B"
		"bet C H D"
		"bet E G H"
		"oppo_side A G H D"
	shows: "ang_eq A G H G H D \<and> ang_eq E G B G H D \<and> ang_suppl B G H G H D"
proof -
	have "col C H D" using collinear_b `axioms` `bet C H D` by blast
	have "G \<noteq> H" using betweennotequal[OF `axioms` `bet E G H`] by blast
	have "A \<noteq> B" using betweennotequal[OF `axioms` `bet A G B`] by blast
	have "C \<noteq> D" using betweennotequal[OF `axioms` `bet C H D`] by blast
	obtain R where "bet A R D \<and> col G H R \<and> \<not> col G H A" using oppositeside_f[OF `axioms` `oppo_side A G H D`] by blast
	have "oppo_side D G H A" using oppositesidesymmetric[OF `axioms` `oppo_side A G H D`] .
	have "\<not> col G H D" using oppositeside_f[OF `axioms` `oppo_side D G H A`] by blast
	have "\<not> col D H G" using NCorder[OF `axioms` `\<not> col G H D`] by blast
	have "col D H C" using collinearorder[OF `axioms` `col C H D`] by blast
	have "H = H" using equalityreflexiveE[OF `axioms`] .
	have "col D H H" using collinear_b `axioms` `H = H` by blast
	have "C \<noteq> H" using betweennotequal[OF `axioms` `bet C H D`] by blast
	have "\<not> col C H G" using NChelper[OF `axioms` `\<not> col D H G` `col D H C` `col D H H` `C \<noteq> H`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "col C H C" using collinear_b `axioms` `C = C` by blast
	have "col C H D" using `col C H D` .
	have "C \<noteq> D" using betweennotequal[OF `axioms` `bet C H D`] by blast
	have "\<not> col C D G" using NChelper[OF `axioms` `\<not> col C H G` `col C H C` `col C H D` `C \<noteq> D`] .
	obtain P Q S where "bet P G Q \<and> ang_eq Q G H G H C \<and> ang_eq Q G H C H G \<and> ang_eq H G Q C H G \<and> ang_eq P G H G H D \<and> ang_eq P G H D H G \<and> ang_eq H G P D H G \<and> parallel P Q C D \<and> seg_eq P G H D \<and> seg_eq G Q C H \<and> seg_eq G S S H \<and> seg_eq P S S D \<and> seg_eq C S S Q \<and> bet P S D \<and> bet C S Q \<and> bet G S H" using Prop31[OF `axioms` `bet C H D` `\<not> col C D G`] by blast
	have "bet P G Q" using `bet P G Q \<and> ang_eq Q G H G H C \<and> ang_eq Q G H C H G \<and> ang_eq H G Q C H G \<and> ang_eq P G H G H D \<and> ang_eq P G H D H G \<and> ang_eq H G P D H G \<and> parallel P Q C D \<and> seg_eq P G H D \<and> seg_eq G Q C H \<and> seg_eq G S S H \<and> seg_eq P S S D \<and> seg_eq C S S Q \<and> bet P S D \<and> bet C S Q \<and> bet G S H` by blast
	have "ang_eq P G H G H D" using `bet P G Q \<and> ang_eq Q G H G H C \<and> ang_eq Q G H C H G \<and> ang_eq H G Q C H G \<and> ang_eq P G H G H D \<and> ang_eq P G H D H G \<and> ang_eq H G P D H G \<and> parallel P Q C D \<and> seg_eq P G H D \<and> seg_eq G Q C H \<and> seg_eq G S S H \<and> seg_eq P S S D \<and> seg_eq C S S Q \<and> bet P S D \<and> bet C S Q \<and> bet G S H` by blast
	have "seg_eq G S S H" using `bet P G Q \<and> ang_eq Q G H G H C \<and> ang_eq Q G H C H G \<and> ang_eq H G Q C H G \<and> ang_eq P G H G H D \<and> ang_eq P G H D H G \<and> ang_eq H G P D H G \<and> parallel P Q C D \<and> seg_eq P G H D \<and> seg_eq G Q C H \<and> seg_eq G S S H \<and> seg_eq P S S D \<and> seg_eq C S S Q \<and> bet P S D \<and> bet C S Q \<and> bet G S H` by blast
	have "seg_eq P S S D" using `bet P G Q \<and> ang_eq Q G H G H C \<and> ang_eq Q G H C H G \<and> ang_eq H G Q C H G \<and> ang_eq P G H G H D \<and> ang_eq P G H D H G \<and> ang_eq H G P D H G \<and> parallel P Q C D \<and> seg_eq P G H D \<and> seg_eq G Q C H \<and> seg_eq G S S H \<and> seg_eq P S S D \<and> seg_eq C S S Q \<and> bet P S D \<and> bet C S Q \<and> bet G S H` by blast
	have "seg_eq C S S Q" using `bet P G Q \<and> ang_eq Q G H G H C \<and> ang_eq Q G H C H G \<and> ang_eq H G Q C H G \<and> ang_eq P G H G H D \<and> ang_eq P G H D H G \<and> ang_eq H G P D H G \<and> parallel P Q C D \<and> seg_eq P G H D \<and> seg_eq G Q C H \<and> seg_eq G S S H \<and> seg_eq P S S D \<and> seg_eq C S S Q \<and> bet P S D \<and> bet C S Q \<and> bet G S H` by blast
	have "bet C S Q" using `bet P G Q \<and> ang_eq Q G H G H C \<and> ang_eq Q G H C H G \<and> ang_eq H G Q C H G \<and> ang_eq P G H G H D \<and> ang_eq P G H D H G \<and> ang_eq H G P D H G \<and> parallel P Q C D \<and> seg_eq P G H D \<and> seg_eq G Q C H \<and> seg_eq G S S H \<and> seg_eq P S S D \<and> seg_eq C S S Q \<and> bet P S D \<and> bet C S Q \<and> bet G S H` by blast
	have "bet G S H" using `bet P G Q \<and> ang_eq Q G H G H C \<and> ang_eq Q G H C H G \<and> ang_eq H G Q C H G \<and> ang_eq P G H G H D \<and> ang_eq P G H D H G \<and> ang_eq H G P D H G \<and> parallel P Q C D \<and> seg_eq P G H D \<and> seg_eq G Q C H \<and> seg_eq G S S H \<and> seg_eq P S S D \<and> seg_eq C S S Q \<and> bet P S D \<and> bet C S Q \<and> bet G S H` by blast
	have "parallel A B C D" using `parallel A B C D` .
	have "\<not> (meets A B C D)" using parallel_f[OF `axioms` `parallel A B C D`] by blast
	have "P = P" using equalityreflexiveE[OF `axioms`] .
	have "P \<noteq> G" using betweennotequal[OF `axioms` `bet P G Q`] by blast
	have "G \<noteq> P" using inequalitysymmetric[OF `axioms` `P \<noteq> G`] .
	have "ray_on G P P" using ray4 `axioms` `P = P` `G \<noteq> P` by blast
	have "bet P S D" using `bet P G Q \<and> ang_eq Q G H G H C \<and> ang_eq Q G H C H G \<and> ang_eq H G Q C H G \<and> ang_eq P G H G H D \<and> ang_eq P G H D H G \<and> ang_eq H G P D H G \<and> parallel P Q C D \<and> seg_eq P G H D \<and> seg_eq G Q C H \<and> seg_eq G S S H \<and> seg_eq P S S D \<and> seg_eq C S S Q \<and> bet P S D \<and> bet C S Q \<and> bet G S H` by blast
	have "bet A R D" using `bet A R D \<and> col G H R \<and> \<not> col G H A` by blast
	have "col G S H" using collinear_b `axioms` `bet P G Q \<and> ang_eq Q G H G H C \<and> ang_eq Q G H C H G \<and> ang_eq H G Q C H G \<and> ang_eq P G H G H D \<and> ang_eq P G H D H G \<and> ang_eq H G P D H G \<and> parallel P Q C D \<and> seg_eq P G H D \<and> seg_eq G Q C H \<and> seg_eq G S S H \<and> seg_eq P S S D \<and> seg_eq C S S Q \<and> bet P S D \<and> bet C S Q \<and> bet G S H` by blast
	have "col G H S" using collinearorder[OF `axioms` `col G S H`] by blast
	have "col G H R" using `bet A R D \<and> col G H R \<and> \<not> col G H A` by blast
	have "\<not> col G H A" using `bet A R D \<and> col G H R \<and> \<not> col G H A` by blast
	have "ang_eq G H D P G H" using equalanglessymmetric[OF `axioms` `ang_eq P G H G H D`] .
	have "\<not> col P G H" using equalanglesNC[OF `axioms` `ang_eq G H D P G H`] .
	have "\<not> col G H P" using NCorder[OF `axioms` `\<not> col P G H`] by blast
	have "same_side A P G H" using sameside_b[OF `axioms` `col G H R` `col G H S` `bet A R D` `bet P S D` `\<not> col G H A` `\<not> col G H P`] .
	have "H = H" using equalityreflexiveE[OF `axioms`] .
	have "G \<noteq> H" using betweennotequal[OF `axioms` `bet E G H`] by blast
	have "ray_on G H H" using ray4 `axioms` `H = H` `G \<noteq> H` by blast
	have "ray_on G P P" using `ray_on G P P` .
	have "\<not> (ang_lt H G A H G P)"
	proof (rule ccontr)
		assume "ang_lt H G A H G P"
		obtain M where "bet P M H \<and> ray_on G A M" using crossbar2[OF `axioms` `ang_lt H G A H G P` `same_side A P G H` `ray_on G H H` `ray_on G P P`]  by  blast
		have "ray_on G A M" using `bet P M H \<and> ray_on G A M` by blast
		have "bet P S D" using `bet P S D` .
		have "bet G S H" using `bet G S H` .
		have "bet P M H" using `bet P M H \<and> ray_on G A M` by blast
		have "seg_eq G S H S" using congruenceflip[OF `axioms` `seg_eq G S S H`] by blast
		have "seg_eq S P S D" using congruenceflip[OF `axioms` `seg_eq P S S D`] by blast
		obtain K where "bet G M K \<and> bet D H K" using Euclid5E[OF `axioms` `bet P S D` `bet G S H` `bet P M H` `seg_eq G S H S` `seg_eq S P S D`]  by  blast
		have "bet G M K" using `bet G M K \<and> bet D H K` by blast
		have "bet D H K" using `bet G M K \<and> bet D H K` by blast
		have "col G A M" using rayimpliescollinear[OF `axioms` `ray_on G A M`] .
		have "col G M K" using collinear_b `axioms` `bet G M K \<and> bet D H K` by blast
		have "col M G A" using collinearorder[OF `axioms` `col G A M`] by blast
		have "col M G K" using collinearorder[OF `axioms` `col G M K`] by blast
		have "G \<noteq> M" using raystrict[OF `axioms` `ray_on G A M`] .
		have "M \<noteq> G" using inequalitysymmetric[OF `axioms` `G \<noteq> M`] .
		have "col G A K" using collinear4[OF `axioms` `col M G A` `col M G K` `M \<noteq> G`] .
		have "col A G B" using collinear_b `axioms` `bet A G B` by blast
		have "col A G K" using collinearorder[OF `axioms` `col G A K`] by blast
		have "col G A B" using collinearorder[OF `axioms` `col A G B`] by blast
		have "col G A K" using collinearorder[OF `axioms` `col A G K`] by blast
		have "A \<noteq> G" using betweennotequal[OF `axioms` `bet A G B`] by blast
		have "G \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> G`] .
		have "col A B K" using collinear4[OF `axioms` `col G A B` `col G A K` `G \<noteq> A`] .
		have "col H D K" using collinear_b `axioms` `bet G M K \<and> bet D H K` by blast
		have "col H D C" using collinearorder[OF `axioms` `col C H D`] by blast
		have "H \<noteq> D" using betweennotequal[OF `axioms` `bet C H D`] by blast
		have "col D K C" using collinear4[OF `axioms` `col H D K` `col H D C` `H \<noteq> D`] .
		have "col C D K" using collinearorder[OF `axioms` `col D K C`] by blast
		have "A \<noteq> B \<and> C \<noteq> D \<and> col A B K \<and> col C D K" using `A \<noteq> B` `C \<noteq> D` `col A B K` `col C D K` by blast
		have "meets A B C D" using meet_b[OF `axioms` `A \<noteq> B` `C \<noteq> D` `col A B K` `col C D K`] .
		show "False" using `meets A B C D` `\<not> (meets A B C D)` by blast
	qed
	hence "\<not> (ang_lt H G A H G P)" by blast
	have "\<not> (ang_lt H G P H G A)"
	proof (rule ccontr)
		assume "ang_lt H G P H G A"
		have "\<not> col P G H" using NCorder[OF `axioms` `\<not> col G H P`] by blast
		have "ang_eq P G H H G P" using ABCequalsCBA[OF `axioms` `\<not> col P G H`] .
		have "ang_lt P G H H G A" using angleorderrespectscongruence2[OF `axioms` `ang_lt H G P H G A` `ang_eq P G H H G P`] .
		have "\<not> (col H G A)"
		proof (rule ccontr)
			assume "col H G A"
			have "col G H A" using collinearorder[OF `axioms` `col H G A`] by blast
			have "\<not> col G H A" using `\<not> col G H A` .
			show "False" using `\<not> col G H A` `col G H A` by blast
		qed
		hence "\<not> col H G A" by blast
		have "ang_eq H G A A G H" using ABCequalsCBA[OF `axioms` `\<not> col H G A`] .
		have "ang_eq A G H H G A" using equalanglessymmetric[OF `axioms` `ang_eq H G A A G H`] .
		have "ang_lt P G H A G H" using angleorderrespectscongruence[OF `axioms` `ang_lt P G H H G A` `ang_eq A G H H G A`] .
		have "H = H" using equalityreflexiveE[OF `axioms`] .
		have "G \<noteq> H" using `G \<noteq> H` .
		have "ray_on G H H" using ray4 `axioms` `H = H` `G \<noteq> H` by blast
		have "bet P G Q" using `bet P G Q` .
		have "linear_pair P G H H Q" using supplement_b[OF `axioms` `ray_on G H H` `bet P G Q`] .
		have "bet D H C" using betweennesssymmetryE[OF `axioms` `bet C H D`] .
		have "G = G" using equalityreflexiveE[OF `axioms`] .
		have "H \<noteq> G" using inequalitysymmetric[OF `axioms` `G \<noteq> H`] .
		have "ray_on H G G" using ray4 `axioms` `G = G` `H \<noteq> G` by blast
		have "linear_pair D H G G C" using supplement_b[OF `axioms` `ray_on H G G` `bet D H C`] .
		have "ang_eq P G H G H D" using `ang_eq P G H G H D` .
		have "ang_eq G H D D H G" using ABCequalsCBA[OF `axioms` `\<not> col G H D`] .
		have "ang_eq P G H D H G" using equalanglestransitive[OF `axioms` `ang_eq P G H G H D` `ang_eq G H D D H G`] .
		have "ang_eq H G Q G H C" using supplements[OF `axioms` `ang_eq P G H D H G` `linear_pair P G H H Q` `linear_pair D H G G C`] .
		have "linear_pair A G H H B" using supplement_b[OF `axioms` `ray_on G H H` `bet A G B`] .
		have "ang_lt H G B H G Q" using supplementinequality[OF `axioms` `linear_pair A G H H B` `linear_pair P G H H Q` `ang_lt P G H A G H`] .
		have "bet B G A" using betweennesssymmetryE[OF `axioms` `bet A G B`] .
		have "G = G" using equalityreflexiveE[OF `axioms`] .
		have "col G H G" using collinear_b `axioms` `G = G` by blast
		have "\<not> (col G H B)"
		proof (rule ccontr)
			assume "col G H B"
			have "col A G B" using collinear_b `axioms` `bet A G B` by blast
			have "col B G A" using collinearorder[OF `axioms` `col A G B`] by blast
			have "col B G H" using collinearorder[OF `axioms` `col G H B`] by blast
			have "G \<noteq> B" using betweennotequal[OF `axioms` `bet A G B`] by blast
			have "B \<noteq> G" using inequalitysymmetric[OF `axioms` `G \<noteq> B`] .
			have "col G A H" using collinear4[OF `axioms` `col B G A` `col B G H` `B \<noteq> G`] .
			have "col H G A" using collinearorder[OF `axioms` `col G A H`] by blast
			show "False" using `col H G A` `\<not> col H G A` by blast
		qed
		hence "\<not> col G H B" by blast
		have "oppo_side B G H A" using oppositeside_b[OF `axioms` `bet B G A` `col G H G` `\<not> col G H B`] .
		have "oppo_side A G H B" using oppositesidesymmetric[OF `axioms` `oppo_side B G H A`] .
		have "same_side A P G H" using sameside_b[OF `axioms` `col G H R` `col G H S` `bet A R D` `bet P S D` `\<not> col G H A` `\<not> col G H P`] .
		have "same_side P A G H" using samesidesymmetric[OF `axioms` `same_side A P G H`] by blast
		have "oppo_side P G H B" using planeseparation[OF `axioms` `same_side P A G H` `oppo_side A G H B`] .
		obtain L where "bet P L B \<and> col G H L \<and> \<not> col G H P" using oppositeside_f[OF `axioms` `oppo_side P G H B`] by blast
		have "bet P L B" using `bet P L B \<and> col G H L \<and> \<not> col G H P` by blast
		have "bet B L P" using betweennesssymmetryE[OF `axioms` `bet P L B`] .
		have "col G H L" using `bet P L B \<and> col G H L \<and> \<not> col G H P` by blast
		have "ang_eq G H C H G Q" using equalanglessymmetric[OF `axioms` `ang_eq H G Q G H C`] .
		have "\<not> col H G Q" using equalanglesNC[OF `axioms` `ang_eq G H C H G Q`] .
		have "\<not> (col G H Q)"
		proof (rule ccontr)
			assume "col G H Q"
			have "col H G Q" using collinearorder[OF `axioms` `col G H Q`] by blast
			show "False" using `col H G Q` `\<not> col H G Q` by blast
		qed
		hence "\<not> col G H Q" by blast
		have "\<not> col G H B" using `\<not> col G H B` .
		have "bet Q G P" using betweennesssymmetryE[OF `axioms` `bet P G Q`] .
		have "same_side B Q G H" using sameside_b[OF `axioms` `col G H L` `col G H G` `bet B L P` `bet Q G P` `\<not> col G H B` `\<not> col G H Q`] .
		have "ang_lt H G B H G Q" using `ang_lt H G B H G Q` .
		have "same_side B Q G H" using `same_side B Q G H` .
		have "ray_on G H H" using `ray_on G H H` .
		have "Q = Q" using equalityreflexiveE[OF `axioms`] .
		have "Q \<noteq> G" using betweennotequal[OF `axioms` `bet Q G P`] by blast
		have "G \<noteq> Q" using inequalitysymmetric[OF `axioms` `Q \<noteq> G`] .
		have "ray_on G Q Q" using ray4 `axioms` `Q = Q` `G \<noteq> Q` by blast
		obtain M where "bet Q M H \<and> ray_on G B M" using crossbar2[OF `axioms` `ang_lt H G B H G Q` `same_side B Q G H` `ray_on G H H` `ray_on G Q Q`]  by  blast
		have "ray_on G B M" using `bet Q M H \<and> ray_on G B M` by blast
		have "seg_eq G S H S" using congruenceflip[OF `axioms` `seg_eq G S S H`] by blast
		have "bet Q S C" using betweennesssymmetryE[OF `axioms` `bet C S Q`] .
		have "bet G S H" using `bet G S H` .
		have "bet Q M H" using `bet Q M H \<and> ray_on G B M` by blast
		have "seg_eq S Q C S" using congruencesymmetric[OF `axioms` `seg_eq C S S Q`] .
		have "seg_eq S Q S C" using congruenceflip[OF `axioms` `seg_eq S Q C S`] by blast
		have "\<not> col G H C" using NCorder[OF `axioms` `\<not> col C H G`] by blast
		obtain K where "bet G M K \<and> bet C H K" using Euclid5E[OF `axioms` `bet Q S C` `bet G S H` `bet Q M H` `seg_eq G S H S` `seg_eq S Q S C`]  by  blast
		have "bet G M K" using `bet G M K \<and> bet C H K` by blast
		have "bet C H K" using `bet G M K \<and> bet C H K` by blast
		have "col G B M" using rayimpliescollinear[OF `axioms` `ray_on G B M`] .
		have "col G M K" using collinear_b `axioms` `bet G M K \<and> bet C H K` by blast
		have "col M G B" using collinearorder[OF `axioms` `col G B M`] by blast
		have "col M G K" using collinearorder[OF `axioms` `col G M K`] by blast
		have "G \<noteq> M" using raystrict[OF `axioms` `ray_on G B M`] .
		have "M \<noteq> G" using inequalitysymmetric[OF `axioms` `G \<noteq> M`] .
		have "col G B K" using collinear4[OF `axioms` `col M G B` `col M G K` `M \<noteq> G`] .
		have "col B G A" using collinear_b `axioms` `bet B G A` by blast
		have "col B G K" using collinearorder[OF `axioms` `col G B K`] by blast
		have "col G B A" using collinearorder[OF `axioms` `col B G A`] by blast
		have "col G B K" using collinearorder[OF `axioms` `col B G K`] by blast
		have "B \<noteq> G" using betweennotequal[OF `axioms` `bet B G A`] by blast
		have "G \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> G`] .
		have "col B A K" using collinear4[OF `axioms` `col G B A` `col G B K` `G \<noteq> B`] .
		have "col A B K" using collinearorder[OF `axioms` `col B A K`] by blast
		have "col H C K" using collinear_b `axioms` `bet G M K \<and> bet C H K` by blast
		have "col H C D" using collinearorder[OF `axioms` `col C H D`] by blast
		have "H \<noteq> C" using betweennotequal[OF `axioms` `bet D H C`] by blast
		have "col C K D" using collinear4[OF `axioms` `col H C K` `col H C D` `H \<noteq> C`] .
		have "col C D K" using collinearorder[OF `axioms` `col C K D`] by blast
		have "col A B K \<and> col C D K" using `col A B K` `col C D K` by blast
		have "meets A B C D" using meet_b[OF `axioms` `A \<noteq> B` `C \<noteq> D` `col A B K` `col C D K`] .
		show "False" using `meets A B C D` `\<not> (meets A B C D)` by blast
	qed
	hence "\<not> (ang_lt H G P H G A)" by blast
	have "\<not> (col H G P)"
	proof (rule ccontr)
		assume "col H G P"
		have "col G H P" using collinearorder[OF `axioms` `col H G P`] by blast
		show "False" using `col G H P` `\<not> col G H P` by blast
	qed
	hence "\<not> col H G P" by blast
	have "\<not> (col H G A)"
	proof (rule ccontr)
		assume "col H G A"
		have "col G H A" using collinearorder[OF `axioms` `col H G A`] by blast
		have "\<not> col G H A" using oppositeside_f[OF `axioms` `oppo_side A G H D`] by blast
		show "False" using `\<not> col G H A` `col G H A` by blast
	qed
	hence "\<not> col H G A" by blast
	have "ang_eq H G A H G P"
	proof (rule ccontr)
		assume "\<not> (ang_eq H G A H G P)"
		have "ang_lt H G A H G P" using angletrichotomy2[OF `axioms` `\<not> col H G A` `\<not> col H G P` `\<not> (ang_eq H G A H G P)` `\<not> (ang_lt H G P H G A)`] .
		have "\<not> (ang_lt H G A H G P)" using `\<not> (ang_lt H G A H G P)` .
		show "False" using `\<not> (ang_lt H G A H G P)` `ang_lt H G A H G P` by blast
	qed
	hence "ang_eq H G A H G P" by blast
	have "ang_eq H G P P G H" using ABCequalsCBA[OF `axioms` `\<not> col H G P`] .
	have "ang_eq P G H G H D" using `ang_eq P G H G H D` .
	have "ang_eq H G P G H D" using equalanglestransitive[OF `axioms` `ang_eq H G P P G H` `ang_eq P G H G H D`] .
	have "ang_eq G H D D H G" using ABCequalsCBA[OF `axioms` `\<not> col G H D`] .
	have "ang_eq H G P D H G" using equalanglestransitive[OF `axioms` `ang_eq H G P G H D` `ang_eq G H D D H G`] .
	have "ang_eq H G A D H G" using equalanglestransitive[OF `axioms` `ang_eq H G A H G P` `ang_eq H G P D H G`] .
	have "\<not> (col A G H)"
	proof (rule ccontr)
		assume "col A G H"
		have "col G H A" using collinearorder[OF `axioms` `col A G H`] by blast
		have "\<not> col G H A" using `\<not> col G H A` .
		show "False" using `\<not> col G H A` `col G H A` by blast
	qed
	hence "\<not> col A G H" by blast
	have "ang_eq A G H H G A" using ABCequalsCBA[OF `axioms` `\<not> col A G H`] .
	have "ang_eq A G H D H G" using equalanglestransitive[OF `axioms` `ang_eq A G H H G A` `ang_eq H G A D H G`] .
	have "\<not> col D H G" using equalanglesNC[OF `axioms` `ang_eq A G H D H G`] .
	have "ang_eq D H G G H D" using ABCequalsCBA[OF `axioms` `\<not> col D H G`] .
	have "ang_eq A G H G H D" using equalanglestransitive[OF `axioms` `ang_eq A G H D H G` `ang_eq D H G G H D`] .
	have "bet A G B" using `bet A G B` .
	have "bet E G H" using `bet E G H` .
	have "bet H G E" using betweennesssymmetryE[OF `axioms` `bet E G H`] .
	have "\<not> col A G H" using `\<not> col A G H` .
	have "ang_eq A G H E G B" using Prop15[OF `axioms` `bet A G B` `bet H G E` `\<not> col A G H`] by blast
	have "ang_eq E G B A G H" using equalanglessymmetric[OF `axioms` `ang_eq A G H E G B`] .
	have "ang_eq E G B G H D" using equalanglestransitive[OF `axioms` `ang_eq E G B A G H` `ang_eq A G H G H D`] .
	have "ang_eq A G H G H D" using `ang_eq A G H G H D` .
	have "H = H" using equalityreflexiveE[OF `axioms`] .
	have "ray_on G H H" using ray4 `axioms` `H = H` `G \<noteq> H` by blast
	have "linear_pair A G H H B" using supplement_b[OF `axioms` `ray_on G H H` `bet A G B`] .
	have "\<not> (col B G H)"
	proof (rule ccontr)
		assume "col B G H"
		have "col A G B" using collinear_b `axioms` `bet A G B` by blast
		have "col B G A" using collinearorder[OF `axioms` `col A G B`] by blast
		have "G \<noteq> B" using betweennotequal[OF `axioms` `bet A G B`] by blast
		have "B \<noteq> G" using inequalitysymmetric[OF `axioms` `G \<noteq> B`] .
		have "col G H A" using collinear4[OF `axioms` `col B G H` `col B G A` `B \<noteq> G`] .
		have "col A G H" using collinearorder[OF `axioms` `col G H A`] by blast
		have "\<not> col A G H" using `\<not> col A G H` .
		show "False" using `\<not> col A G H` `col A G H` by blast
	qed
	hence "\<not> col B G H" by blast
	have "ang_eq B G H B G H" using equalanglesreflexive[OF `axioms` `\<not> col B G H`] .
	have "ang_eq G H D A G H" using equalanglessymmetric[OF `axioms` `ang_eq A G H G H D`] .
	have "ang_eq A G H H G A" using ABCequalsCBA[OF `axioms` `\<not> col A G H`] .
	have "ang_eq G H D H G A" using equalanglestransitive[OF `axioms` `ang_eq G H D A G H` `ang_eq A G H H G A`] .
	have "linear_pair B G H H A" using supplementsymmetric[OF `axioms` `linear_pair A G H H B`] .
	have "ang_suppl B G H G H D" using tworightangles_b[OF `axioms` `linear_pair B G H H A` `ang_eq B G H B G H` `ang_eq G H D H G A`] .
	have "ang_eq A G H G H D \<and> ang_eq E G B G H D \<and> ang_suppl B G H G H D" using `ang_eq A G H G H D` `ang_eq E G B G H D` `ang_suppl B G H G H D` by blast
	thus ?thesis by blast
qed

end