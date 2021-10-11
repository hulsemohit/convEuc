theory Prop30B
	imports n3_5b Geometry NChelper NCorder Prop28A Prop29 betweennotequal collinear4 collinearorder equalanglesflip equalangleshelper equalanglessymmetric equalanglestransitive inequalitysymmetric parallelflip parallelsymmetric ray4 ray5 samesidesymmetric
begin

theorem(in euclidean_geometry) Prop30B:
	assumes 
		"parallel A B E F"
		"parallel C D E F"
		"bet G K H"
		"bet A G B"
		"bet E H F"
		"bet C K D"
		"oppo_side A G H F"
		"oppo_side C K H F"
	shows "parallel A B C D"
proof -
	have "G \<noteq> H" using betweennotequal[OF `bet G K H`] by blast
	have "H \<noteq> G" using inequalitysymmetric[OF `G \<noteq> H`] .
	have "K \<noteq> H" using betweennotequal[OF `bet G K H`] by blast
	have "H \<noteq> K" using inequalitysymmetric[OF `K \<noteq> H`] .
	obtain P where "bet H G P \<and> seg_eq G P G H" using extensionE[OF `H \<noteq> G` `G \<noteq> H`]  by  blast
	have "bet H G P" using `bet H G P \<and> seg_eq G P G H` by blast
	have "bet P G H" using betweennesssymmetryE[OF `bet H G P`] .
	have "ang_eq A G H G H F" using Prop29[OF `parallel A B E F` `bet A G B` `bet E H F` `bet P G H` `oppo_side A G H F`] by blast
	have "bet P K H" using n3_5b[OF `bet P G H` `bet G K H`] .
	have "ang_eq C K H K H F" using Prop29[OF `parallel C D E F` `bet C K D` `bet E H F` `bet G K H` `oppo_side C K H F`] by blast
	have "bet H K G" using betweennesssymmetryE[OF `bet G K H`] .
	have "ray_on H K G" using ray4 `bet H K G` `H \<noteq> K` by blast
	have "ray_on H G K" using ray5[OF `ray_on H K G`] .
	have "F = F" using equalityreflexiveE.
	have "H \<noteq> F" using betweennotequal[OF `bet E H F`] by blast
	have "ray_on H F F" using ray4 `F = F` `H \<noteq> F` by blast
	have "ang_eq A G H K H F" using equalangleshelper[OF `ang_eq A G H G H F` `ray_on H G K` `ray_on H F F`] .
	have "ang_eq K H F A G H" using equalanglessymmetric[OF `ang_eq A G H K H F`] .
	have "ang_eq C K H A G H" using equalanglestransitive[OF `ang_eq C K H K H F` `ang_eq K H F A G H`] .
	have "G \<noteq> H" using betweennotequal[OF `bet G K H`] by blast
	have "ray_on G H K" using ray4 `bet G K H` `G \<noteq> H` by blast
	have "A \<noteq> G" using betweennotequal[OF `bet A G B`] by blast
	have "G \<noteq> A" using inequalitysymmetric[OF `A \<noteq> G`] .
	have "A = A" using equalityreflexiveE.
	have "ray_on G A A" using ray4 `A = A` `G \<noteq> A` by blast
	have "ang_eq C K H A G K" using equalangleshelper[OF `ang_eq C K H A G H` `ray_on G A A` `ray_on G H K`] .
	have "ang_eq H K C K G A" using equalanglesflip[OF `ang_eq C K H A G K`] .
	have "oppo_side A G H F" using `oppo_side A G H F` .
	have "oppo_side C K H F" using `oppo_side C K H F` .
	obtain M where "bet A M F \<and> col G H M \<and> \<not> col G H A" using oppositeside_f[OF `oppo_side A G H F`]  by  blast
	obtain m where "bet C m F \<and> col K H m \<and> \<not> col K H C" using oppositeside_f[OF `oppo_side C K H F`]  by  blast
	have "bet A M F" using `bet A M F \<and> col G H M \<and> \<not> col G H A` by blast
	have "col G H M" using `bet A M F \<and> col G H M \<and> \<not> col G H A` by blast
	have "\<not> col G H A" using `bet A M F \<and> col G H M \<and> \<not> col G H A` by blast
	have "bet C m F" using `bet C m F \<and> col K H m \<and> \<not> col K H C` by blast
	have "col K H m" using `bet C m F \<and> col K H m \<and> \<not> col K H C` by blast
	have "col G K H" using collinear_b `bet G K H` by blast
	have "col H G K" using collinearorder[OF `col G K H`] by blast
	have "col H G M" using collinearorder[OF `col G H M`] by blast
	have "H \<noteq> G" using betweennotequal[OF `bet H G P`] by blast
	have "col G K M" using collinear4[OF `col H G K` `col H G M` `H \<noteq> G`] .
	have "col K G M" using collinearorder[OF `col G K M`] by blast
	have "col H K m" using collinearorder[OF `col K H m`] by blast
	have "col H K G" using collinearorder[OF `col G K H`] by blast
	have "H \<noteq> K" using betweennotequal[OF `bet H K G`] by blast
	have "col K m G" using collinear4[OF `col H K m` `col H K G` `H \<noteq> K`] .
	have "col K G m" using collinearorder[OF `col K m G`] by blast
	have "col G H K" using collinearorder[OF `col G K H`] by blast
	have "G = G" using equalityreflexiveE.
	have "col G H G" using collinear_b `G = G` by blast
	have "G \<noteq> K" using betweennotequal[OF `bet G K H`] by blast
	have "\<not> col G K A" using NChelper[OF `\<not> col G H A` `col G H G` `col G H K` `G \<noteq> K`] .
	have "\<not> col K G A" using NCorder[OF `\<not> col G K A`] by blast
	have "\<not> col K H C" using `bet C m F \<and> col K H m \<and> \<not> col K H C` by blast
	have "col K H G" using collinearorder[OF `col G H K`] by blast
	have "K = K" using equalityreflexiveE.
	have "col K H K" using collinear_b `K = K` by blast
	have "G \<noteq> K" using betweennotequal[OF `bet G K H`] by blast
	have "K \<noteq> G" using inequalitysymmetric[OF `G \<noteq> K`] .
	have "\<not> col K G C" using NChelper[OF `\<not> col K H C` `col K H K` `col K H G` `K \<noteq> G`] .
	have "col K G M \<and> col K G m \<and> bet A M F \<and> bet C m F \<and> \<not> col K G A \<and> \<not> col K G C" using `col K G M` `col K G m` `bet A M F \<and> col G H M \<and> \<not> col G H A` `bet C m F \<and> col K H m \<and> \<not> col K H C` `\<not> col K G A` `\<not> col K G C` by blast
	have "same_side A C K G" using sameside_b[OF `col K G M` `col K G m` `bet A M F` `bet C m F` `\<not> col K G A` `\<not> col K G C`] .
	have "same_side C A K G" using samesidesymmetric[OF `same_side A C K G`] by blast
	have "bet D K C" using betweennesssymmetryE[OF `bet C K D`] .
	have "bet B G A" using betweennesssymmetryE[OF `bet A G B`] .
	have "bet H K G" using `bet H K G` .
	have "ang_eq H K C K G A" using `ang_eq H K C K G A` .
	have "parallel D C B A" using Prop28A[OF `bet D K C` `bet B G A` `bet H K G` `ang_eq H K C K G A` `same_side C A K G`] .
	have "parallel C D A B" using parallelflip[OF `parallel D C B A`] by blast
	have "parallel A B C D" using parallelsymmetric[OF `parallel C D A B`] .
	thus ?thesis by blast
qed

end