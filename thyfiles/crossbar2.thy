theory crossbar2
	imports Geometry Prop04 Prop07 angledistinct betweennotequal collinear4 collinearorder congruenceflip congruencesymmetric crossbar equalanglesNC equalangleshelper equalanglesreflexive equalanglessymmetric equalanglestransitive equalitysymmetric inequalitysymmetric layoff ray3 ray4 ray5 rayimpliescollinear raystrict sameside2 samesidesymmetric
begin

theorem(in euclidean_geometry) crossbar2:
	assumes 
		"ang_lt H G A H G P"
		"same_side A P G H"
		"ray_on G H S"
		"ray_on G P T"
	shows "\<exists> M. bet T M S \<and> ray_on G A M"
proof -
	have "\<not> col G H P" using sameside_f[OF `same_side A P G H`] by blast
	obtain J K L where "bet L K J \<and> ray_on G H L \<and> ray_on G P J \<and> ang_eq H G A H G K" using anglelessthan_f[OF `ang_lt H G A H G P`]  by  blast
	have "bet L K J" using `bet L K J \<and> ray_on G H L \<and> ray_on G P J \<and> ang_eq H G A H G K` by blast
	have "ray_on G H L" using `bet L K J \<and> ray_on G H L \<and> ray_on G P J \<and> ang_eq H G A H G K` by blast
	have "ray_on G P J" using `bet L K J \<and> ray_on G H L \<and> ray_on G P J \<and> ang_eq H G A H G K` by blast
	have "ang_eq H G A H G K" using `bet L K J \<and> ray_on G H L \<and> ray_on G P J \<and> ang_eq H G A H G K` by blast
	have "\<not> col H G K" using equalanglesNC[OF `ang_eq H G A H G K`] .
	have "\<not> (col L G J)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col L G J))"
hence "col L G J" by blast
		have "col G H L" using rayimpliescollinear[OF `ray_on G H L`] .
		have "col G P J" using rayimpliescollinear[OF `ray_on G P J`] .
		have "col L G H" using collinearorder[OF `col G H L`] by blast
		have "G \<noteq> L" using raystrict[OF `ray_on G H L`] .
		have "L \<noteq> G" using inequalitysymmetric[OF `G \<noteq> L`] .
		have "col G J H" using collinear4[OF `col L G J` `col L G H` `L \<noteq> G`] .
		have "col J G H" using collinearorder[OF `col G J H`] by blast
		have "col J G P" using collinearorder[OF `col G P J`] by blast
		have "G \<noteq> J" using raystrict[OF `ray_on G P J`] .
		have "J \<noteq> G" using inequalitysymmetric[OF `G \<noteq> J`] .
		have "col G H P" using collinear4[OF `col J G H` `col J G P` `J \<noteq> G`] .
		have "\<not> col G H P" using `\<not> col G H P` .
		show "False" using `\<not> col G H P` `col G H P` by blast
	qed
	hence "\<not> col L G J" by blast
	have "triangle L G J" using triangle_b[OF `\<not> col L G J`] .
	have "ray_on G P T" using `ray_on G P T` .
	have "ray_on G P J" using `ray_on G P J` .
	have "ray_on G J T" using ray3[OF `ray_on G P J` `ray_on G P T`] .
	have "ray_on G L S" using ray3[OF `ray_on G H L` `ray_on G H S`] .
	obtain M where "ray_on G K M \<and> bet S M T" using crossbar[OF `triangle L G J` `bet L K J` `ray_on G L S` `ray_on G J T`]  by  blast
	have "ray_on G K M" using `ray_on G K M \<and> bet S M T` by blast
	have "bet S M T" using `ray_on G K M \<and> bet S M T` by blast
	have "bet T M S" using betweennesssymmetryE[OF `bet S M T`] .
	have "ang_eq H G K H G A" using equalanglessymmetric[OF `ang_eq H G A H G K`] .
	have "G \<noteq> A" using angledistinct[OF `ang_eq H G A H G K`] by blast
	have "G \<noteq> M" using raystrict[OF `ray_on G K M`] .
	obtain N where "ray_on G A N \<and> seg_eq G N G M" using layoff[OF `G \<noteq> A` `G \<noteq> M`]  by  blast
	have "ray_on G A N" using `ray_on G A N \<and> seg_eq G N G M` by blast
	have "H = H" using equalityreflexiveE.
	have "\<not> (G = H)"
	proof (rule ccontr)
		assume "\<not> (G \<noteq> H)"
		hence "G = H" by blast
		have "col G H P" using collinear_b `G = H` by blast
		show "False" using `col G H P` `\<not> col G H P` by blast
	qed
	hence "G \<noteq> H" by blast
	have "ray_on G H H" using ray4 `H = H` `G \<noteq> H` by blast
	have "\<not> (col H G M)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col H G M))"
hence "col H G M" by blast
		have "col G K M" using rayimpliescollinear[OF `ray_on G K M`] .
		have "col M G K" using collinearorder[OF `col G K M`] by blast
		have "col M G H" using collinearorder[OF `col H G M`] by blast
		have "G \<noteq> M" using raystrict[OF `ray_on G K M`] .
		have "M \<noteq> G" using inequalitysymmetric[OF `G \<noteq> M`] .
		have "col G K H" using collinear4[OF `col M G K` `col M G H` `M \<noteq> G`] .
		have "col H G K" using collinearorder[OF `col G K H`] by blast
		have "\<not> col H G K" using `\<not> col H G K` .
		show "False" using `\<not> col H G K` `col H G K` by blast
	qed
	hence "\<not> col H G M" by blast
	have "ang_eq H G M H G M" using equalanglesreflexive[OF `\<not> col H G M`] .
	have "ray_on G M K" using ray5[OF `ray_on G K M`] .
	have "ang_eq H G M H G K" using equalangleshelper[OF `ang_eq H G M H G M` `ray_on G H H` `ray_on G M K`] .
	have "ang_eq H G M H G A" using equalanglestransitive[OF `ang_eq H G M H G K` `ang_eq H G K H G A`] .
	have "\<not> col H G A" using equalanglesNC[OF `ang_eq H G K H G A`] .
	have "ang_eq H G A H G A" using equalanglesreflexive[OF `\<not> col H G A`] .
	have "ang_eq H G A H G N" using equalangleshelper[OF `ang_eq H G A H G A` `ray_on G H H` `ray_on G A N`] .
	have "ang_eq H G M H G N" using equalanglestransitive[OF `ang_eq H G M H G A` `ang_eq H G A H G N`] .
	have "ang_eq H G N H G M" using equalanglessymmetric[OF `ang_eq H G M H G N`] .
	have "seg_eq G N G M" using `ray_on G A N \<and> seg_eq G N G M` by blast
	have "seg_eq G H G H" using congruencereflexiveE.
	have "seg_eq H N H M" using Prop04[OF `seg_eq G H G H` `seg_eq G N G M` `ang_eq H G N H G M`] by blast
	have "same_side A P G H" using `same_side A P G H` .
	have "ray_on G P T" using `ray_on G P T` .
	have "G = G" using equalityreflexiveE.
	have "col G G H" using collinear_b `G = G` by blast
	have "same_side A T G H" using sameside2[OF `same_side A P G H` `col G G H` `ray_on G P T`] .
	have "bet S M T" using `bet S M T` .
	have "S \<noteq> M" using betweennotequal[OF `bet S M T`] by blast
	have "ray_on S M T" using ray4 `ray_on G K M \<and> bet S M T` `S \<noteq> M` by blast
	have "ray_on S T M" using ray5[OF `ray_on S M T`] .
	have "col G H S" using rayimpliescollinear[OF `ray_on G H S`] .
	have "col G S H" using collinearorder[OF `col G H S`] by blast
	have "same_side A M G H" using sameside2[OF `same_side A T G H` `col G S H` `ray_on S T M`] .
	have "same_side M A G H" using samesidesymmetric[OF `same_side A M G H`] by blast
	have "ray_on G A N" using `ray_on G A N` .
	have "same_side M N G H" using sameside2[OF `same_side M A G H` `col G G H` `ray_on G A N`] .
	have "seg_eq N H M H" using congruenceflip[OF `seg_eq H N H M`] by blast
	have "seg_eq M H N H" using congruencesymmetric[OF `seg_eq N H M H`] .
	have "seg_eq N G M G" using congruenceflip[OF `seg_eq G N G M`] by blast
	have "seg_eq M G N G" using congruencesymmetric[OF `seg_eq N G M G`] .
	have "G \<noteq> H" using `G \<noteq> H` .
	have "M = N" using Prop07[OF `G \<noteq> H` `seg_eq M G N G` `seg_eq M H N H` `same_side M N G H`] .
	have "N = M" using equalitysymmetric[OF `M = N`] .
	have "ray_on G A M" using `ray_on G A N` `N = M` by blast
	have "bet T M S \<and> ray_on G A M" using `bet T M S` `ray_on G A M` by blast
	thus ?thesis by blast
qed

end