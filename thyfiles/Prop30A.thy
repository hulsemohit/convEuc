theory Prop30A
	imports Axioms Definitions Theorems
begin

theorem Prop30A:
	assumes: `axioms`
		"parallel A B E F"
		"parallel C D E F"
		"bet G H K"
		"bet A G B"
		"bet E H F"
		"bet C K D"
		"oppo_side A G H F"
		"oppo_side F H K C"
	shows: "parallel A B C D"
proof -
	have "parallel E F C D" using parallelsymmetric[OF `axioms` `parallel C D E F`] .
	have "G \<noteq> H" using betweennotequal[OF `axioms` `bet G H K`] by blast
	have "H \<noteq> G" using inequalitysymmetric[OF `axioms` `G \<noteq> H`] .
	obtain P where "bet H G P \<and> seg_eq G P G H" using extensionE[OF `axioms` `H \<noteq> G` `G \<noteq> H`]  by  blast
	have "bet H G P" using `bet H G P \<and> seg_eq G P G H` by blast
	have "bet P G H" using betweennesssymmetryE[OF `axioms` `bet H G P`] .
	have "bet P G K" using n3_7b[OF `axioms` `bet P G H` `bet G H K`] .
	obtain M where "bet A M F \<and> col G H M \<and> \<not> col G H A" sorry
	obtain N where "bet F N C \<and> col H K N \<and> \<not> col H K F" sorry
	have "col G H M" using `bet A M F \<and> col G H M \<and> \<not> col G H A` by blast
	have "\<not> (meets C D E F)" sorry
	have "\<not> col G H A" sorry
	have "A \<noteq> G" using betweennotequal[OF `axioms` `bet A G B`] by blast
	have "G \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> G`] .
	have "G \<noteq> H" using betweennotequal[OF `axioms` `bet G H K`] by blast
	have "\<not> col A G H" using NCorder[OF `axioms` `\<not> col G H A`] by blast
	have "ang_eq A G H G H F" using Prop29[OF `axioms` `parallel A B E F` `bet A G B` `bet E H F` `bet P G H` `oppo_side A G H F`] by blast
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "ray_on G A A" using ray4 `axioms` `A = A` `G \<noteq> A` by blast
	have "ray_on G H K" using ray4 `axioms` `bet G H K` `G \<noteq> H` by blast
	have "\<not> col A G H" using `\<not> col A G H` .
	have "ang_eq A G H A G H" using equalanglesreflexive[OF `axioms` `\<not> col A G H`] .
	have "ang_eq A G H A G K" using equalangleshelper[OF `axioms` `ang_eq A G H A G H` `ray_on G A A` `ray_on G H K`] .
	have "ang_eq A G K A G H" using equalanglessymmetric[OF `axioms` `ang_eq A G H A G K`] .
	have "ang_eq A G K G H F" using equalanglestransitive[OF `axioms` `ang_eq A G K A G H` `ang_eq A G H G H F`] .
	have "bet F N C" using `bet F N C \<and> col H K N \<and> \<not> col H K F` by blast
	have "bet C N F" using betweennesssymmetryE[OF `axioms` `bet F N C`] .
	have "parallel E F C D" using `parallel E F C D` .
	have "bet E H F" using `bet E H F` .
	have "bet G H K" using `bet G H K` .
	have "H = H" using equalityreflexiveE[OF `axioms`] .
	have "\<not> col H K F" using `bet F N C \<and> col H K N \<and> \<not> col H K F` by blast
	have "\<not> col F H K" using NCorder[OF `axioms` `\<not> col H K F`] by blast
	have "col E H F" using col_b `axioms` `bet E H F` by blast
	have "col F H E" using collinearorder[OF `axioms` `col E H F`] by blast
	have "col F H H" using col_b `axioms` `H = H` by blast
	have "E \<noteq> H" using betweennotequal[OF `axioms` `bet E H F`] by blast
	have "\<not> col E H K" using NChelper[OF `axioms` `\<not> col F H K` `col F H E` `col F H H` `E \<noteq> H`] .
	have "col E H F" using col_b `axioms` `bet E H F` by blast
	have "col E H H" using col_b `axioms` `H = H` by blast
	have "H \<noteq> F" using betweennotequal[OF `axioms` `bet E H F`] by blast
	have "F \<noteq> H" using inequalitysymmetric[OF `axioms` `H \<noteq> F`] .
	have "\<not> col F H K" using NChelper[OF `axioms` `\<not> col E H K` `col E H F` `col E H H` `F \<noteq> H`] .
	have "\<not> col H K F" using NCorder[OF `axioms` `\<not> col F H K`] by blast
	have "col H K N" using `bet F N C \<and> col H K N \<and> \<not> col H K F` by blast
	have "H = H" using equalityreflexiveE[OF `axioms`] .
	have "col H K H" using col_b `axioms` `H = H` by blast
	have "col K H N" using collinearorder[OF `axioms` `col H K N`] by blast
	have "\<not> (meets C D E F)" using `\<not> (meets C D E F)` .
	have "bet C N F" using `bet C N F` .
	have "bet C K D" using `bet C K D` .
	have "bet E H F" using `bet E H F` .
	have "col C K D" using col_b `axioms` `bet C K D` by blast
	have "col E H F" using col_b `axioms` `bet E H F` by blast
	have "C \<noteq> K" using betweennotequal[OF `axioms` `bet C K D`] by blast
	have "C \<noteq> D" using betweennotequal[OF `axioms` `bet C K D`] by blast
	have "H \<noteq> F" using betweennotequal[OF `axioms` `bet E H F`] by blast
	have "E \<noteq> F" using betweennotequal[OF `axioms` `bet E H F`] by blast
	have "bet K N H" using collinearbetween[OF `axioms` `col C K D` `col E H F` `C \<noteq> D` `E \<noteq> F` `C \<noteq> K` `H \<noteq> F` `\<not> (meets C D E F)` `bet C N F` `col K H N`] .
	have "N \<noteq> H" using betweennotequal[OF `axioms` `bet K N H`] by blast
	have "H \<noteq> N" using inequalitysymmetric[OF `axioms` `N \<noteq> H`] .
	have "\<not> col H N F" using NChelper[OF `axioms` `\<not> col H K F` `col H K H` `col H K N` `H \<noteq> N`] .
	have "\<not> col F N H" using NCorder[OF `axioms` `\<not> col H N F`] by blast
	have "bet F N C" using betweennesssymmetryE[OF `axioms` `bet C N F`] .
	have "col F N C" using col_b `axioms` `bet F N C \<and> col H K N \<and> \<not> col H K F` by blast
	have "N = N" using equalityreflexiveE[OF `axioms`] .
	have "col F N N" using col_b `axioms` `N = N` by blast
	have "C \<noteq> N" using betweennotequal[OF `axioms` `bet C N F`] by blast
	have "\<not> col C N H" using NChelper[OF `axioms` `\<not> col F N H` `col F N C` `col F N N` `C \<noteq> N`] .
	have "\<not> col H N C" using NCorder[OF `axioms` `\<not> col C N H`] by blast
	have "bet H N K" using betweennesssymmetryE[OF `axioms` `bet K N H`] .
	have "col H N K" using col_b `axioms` `bet H N K` by blast
	have "col H N H" using col_b `axioms` `H = H` by blast
	have "H \<noteq> K" using betweennotequal[OF `axioms` `bet G H K`] by blast
	have "\<not> col H K C" using NChelper[OF `axioms` `\<not> col H N C` `col H N H` `col H N K` `H \<noteq> K`] .
	have "\<not> col H K E" using NCorder[OF `axioms` `\<not> col E H K`] by blast
	have "same_side E C H K" sorry
	have "K = K" using equalityreflexiveE[OF `axioms`] .
	have "col H K K" using col_b `axioms` `K = K` by blast
	have "oppo_side C H K D" sorry
	have "oppo_side E H K D" using planeseparation[OF `axioms` `same_side E C H K` `oppo_side C H K D`] .
	have "ang_eq G H F H K D" using Prop29[OF `axioms` `parallel E F C D` `bet E H F` `bet C K D` `bet G H K` `oppo_side E H K D`] by blast
	have "\<not> col C K H" using NCorder[OF `axioms` `\<not> col H K C`] by blast
	have "col C K D" using col_b `axioms` `bet C K D` by blast
	have "K = K" using equalityreflexiveE[OF `axioms`] .
	have "col C K K" using col_b `axioms` `K = K` by blast
	have "K \<noteq> D" using betweennotequal[OF `axioms` `bet C K D`] by blast
	have "D \<noteq> K" using inequalitysymmetric[OF `axioms` `K \<noteq> D`] .
	have "\<not> col D K H" using NChelper[OF `axioms` `\<not> col C K H` `col C K D` `col C K K` `D \<noteq> K`] .
	have "\<not> col H K D" using NCorder[OF `axioms` `\<not> col D K H`] by blast
	have "ang_eq H K D H K D" using equalanglesreflexive[OF `axioms` `\<not> col H K D`] .
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "ray_on K D D" using ray4 `axioms` `D = D` `K \<noteq> D` by blast
	have "bet K H G" using betweennesssymmetryE[OF `axioms` `bet G H K`] .
	have "K \<noteq> H" using betweennotequal[OF `axioms` `bet K H G`] by blast
	have "ray_on K H G" using ray4 `axioms` `bet K H G` `K \<noteq> H` by blast
	have "ang_eq H K D G K D" using equalangleshelper[OF `axioms` `ang_eq H K D H K D` `ray_on K H G` `ray_on K D D`] .
	have "ang_eq G H F G K D" using equalanglestransitive[OF `axioms` `ang_eq G H F H K D` `ang_eq H K D G K D`] .
	have "ang_eq A G K G K D" using equalanglestransitive[OF `axioms` `ang_eq A G K G H F` `ang_eq G H F G K D`] .
	have "col G H K" using col_b `axioms` `bet G H K` by blast
	have "G \<noteq> H" using betweennotequal[OF `axioms` `bet G H K`] by blast
	have "col H M K" using collinear4[OF `axioms` `col G H M` `col G H K` `G \<noteq> H`] .
	have "col H K M" using collinearorder[OF `axioms` `col H M K`] by blast
	have "col H K G" using collinearorder[OF `axioms` `col G H K`] by blast
	have "H \<noteq> K" using betweennotequal[OF `axioms` `bet G H K`] by blast
	have "col K M G" using collinear4[OF `axioms` `col H K M` `col H K G` `H \<noteq> K`] .
	have "col G K M" using collinearorder[OF `axioms` `col K M G`] by blast
	have "col H K N" using `col H K N` .
	have "col H K G" using collinearorder[OF `axioms` `col G H K`] by blast
	have "col K N G" using collinear4[OF `axioms` `col H K N` `col H K G` `H \<noteq> K`] .
	have "col G K N" using collinearorder[OF `axioms` `col K N G`] by blast
	have "bet C N F" using `bet C N F` .
	have "bet A M F" using `bet A M F \<and> col G H M \<and> \<not> col G H A` by blast
	have "\<not> col A G K" using equalanglesNC[OF `axioms` `ang_eq A G H A G K`] .
	have "\<not> col G K A" using NCorder[OF `axioms` `\<not> col A G K`] by blast
	have "\<not> col H K C" using NCorder[OF `axioms` `\<not> col C K H`] by blast
	have "col H K G" using collinearorder[OF `axioms` `col G H K`] by blast
	have "col H K K" using col_b `axioms` `K = K` by blast
	have "G \<noteq> K" using betweennotequal[OF `axioms` `bet G H K`] by blast
	have "\<not> col G K C" using NChelper[OF `axioms` `\<not> col H K C` `col H K G` `col H K K` `G \<noteq> K`] .
	have "same_side A C G K" sorry
	have "col G K K" using col_b `axioms` `K = K` by blast
	have "oppo_side C G K D" sorry
	have "oppo_side A G K D" using planeseparation[OF `axioms` `same_side A C G K` `oppo_side C G K D`] .
	have "parallel A B C D" using Prop27[OF `axioms` `bet A G B` `bet C K D` `ang_eq A G K G K D` `oppo_side A G K D`] .
	thus ?thesis by blast
qed

end