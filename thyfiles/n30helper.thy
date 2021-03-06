theory n30helper
	imports n3_6a Geometry NCorder betweennotequal collinear4 collinearbetween collinearorder collinearparallel crisscross inequalitysymmetric parallelNC parallelflip parallelsymmetric
begin

theorem(in euclidean_geometry) n30helper:
	assumes 
		"parallel A B E F"
		"bet A G B"
		"bet E H F"
		"\<not> (cross A F G H)"
	shows "cross A E G H"
proof -
	have "col A G B" using collinear_b `bet A G B` by blast
	have "col E H F" using collinear_b `bet E H F` by blast
	have "col B A G" using collinearorder[OF `col A G B`] by blast
	have "col E F H" using collinearorder[OF `col E H F`] by blast
	have "H \<noteq> F" using betweennotequal[OF `bet E H F`] by blast
	have "E \<noteq> H" using betweennotequal[OF `bet E H F`] by blast
	have "H \<noteq> E" using inequalitysymmetric[OF `E \<noteq> H`] .
	have "F \<noteq> H" using inequalitysymmetric[OF `H \<noteq> F`] .
	have "A \<noteq> G" using betweennotequal[OF `bet A G B`] by blast
	have "G \<noteq> A" using inequalitysymmetric[OF `A \<noteq> G`] .
	have "parallel A B F E" using parallelflip[OF `parallel A B E F`] by blast
	have "col F E H" using collinearorder[OF `col E F H`] by blast
	have "parallel A B H E" using collinearparallel[OF `parallel A B F E` `col F E H` `H \<noteq> E`] .
	have "parallel A B H F" using collinearparallel[OF `parallel A B E F` `col E F H` `H \<noteq> F`] .
	have "parallel H F A B" using parallelsymmetric[OF `parallel A B H F`] .
	have "parallel H F B A" using parallelflip[OF `parallel H F A B`] by blast
	have "parallel H F G A" using collinearparallel[OF `parallel H F B A` `col B A G` `G \<noteq> A`] .
	have "parallel H F A G" using parallelflip[OF `parallel H F G A`] by blast
	have "parallel A G H F" using parallelsymmetric[OF `parallel H F A G`] .
	have "parallel A G F H" using parallelflip[OF `parallel A G H F`] by blast
	have "cross A H F G" using crisscross[OF `parallel A G F H` `\<not> (cross A F G H)`] .
	obtain M where "bet A M H \<and> bet F M G" using cross_f[OF `cross A H F G`]  by  blast
	have "bet A M H" using `bet A M H \<and> bet F M G` by blast
	have "\<not> col A E F" using parallelNC[OF `parallel A B E F`] by blast
	have "\<not> col F E A" using NCorder[OF `\<not> col A E F`] by blast
	have "bet F H E" using betweennesssymmetryE[OF `bet E H F`] .
	obtain p where "bet A p E \<and> bet F M p" using Pasch_outerE[OF `bet A M H` `bet F H E` `\<not> col F E A`]  by  blast
	have "bet A p E" using `bet A p E \<and> bet F M p` by blast
	have "bet F M p" using `bet A p E \<and> bet F M p` by blast
	have "bet F M G" using `bet A M H \<and> bet F M G` by blast
	have "col F M G" using collinear_b `bet A M H \<and> bet F M G` by blast
	have "col F M p" using collinear_b `bet A p E \<and> bet F M p` by blast
	have "F \<noteq> M" using betweennotequal[OF `bet F M G`] by blast
	have "col M G p" using collinear4[OF `col F M G` `col F M p` `F \<noteq> M`] .
	have "col M p G" using collinearorder[OF `col M G p`] by blast
	have "col M p F" using collinearorder[OF `col F M p`] by blast
	have "M \<noteq> p" using betweennotequal[OF `bet F M p`] by blast
	have "col p G F" using collinear4[OF `col M p G` `col M p F` `M \<noteq> p`] .
	have "col G F p" using collinearorder[OF `col p G F`] by blast
	have "col A G B" using `col A G B` .
	have "col H F E" using collinearorder[OF `col E F H`] by blast
	have "A \<noteq> B" using betweennotequal[OF `bet A G B`] by blast
	have "A \<noteq> G" using betweennotequal[OF `bet A G B`] by blast
	have "E \<noteq> F" using betweennotequal[OF `bet E H F`] by blast
	have "F \<noteq> E" using inequalitysymmetric[OF `E \<noteq> F`] .
	have "parallel A B H E" using `parallel A B H E` .
	have "\<not> (meets A B H E)" using parallel_f[OF `parallel A B H E`] by fastforce
	have "bet G p F" using collinearbetween[OF `col A G B` `col H F E` `A \<noteq> B` `H \<noteq> E` `A \<noteq> G` `F \<noteq> E` `\<not> (meets A B H E)` `bet A p E` `col G F p`] .
	have "bet F M p" using `bet F M p` .
	have "bet F p G" using betweennesssymmetryE[OF `bet G p F`] .
	have "bet M p G" using n3_6a[OF `bet F M p` `bet F p G`] .
	have "bet G p M" using betweennesssymmetryE[OF `bet M p G`] .
	have "\<not> col A G H" using parallelNC[OF `parallel A G F H`] by blast
	have "\<not> col A H G" using NCorder[OF `\<not> col A G H`] by blast
	obtain m where "bet G m H \<and> bet A p m" using Pasch_outerE[OF `bet G p M` `bet A M H` `\<not> col A H G`]  by  blast
	have "bet G m H" using `bet G m H \<and> bet A p m` by blast
	have "bet A p m" using `bet G m H \<and> bet A p m` by blast
	have "col A p m" using collinear_b `bet G m H \<and> bet A p m` by blast
	have "col A p E" using collinear_b `bet A p E \<and> bet F M p` by blast
	have "A \<noteq> p" using betweennotequal[OF `bet A p E`] by blast
	have "col p m E" using collinear4[OF `col A p m` `col A p E` `A \<noteq> p`] .
	have "col p m A" using collinearorder[OF `col A p m`] by blast
	have "p \<noteq> m" using betweennotequal[OF `bet A p m`] by blast
	have "col m E A" using collinear4[OF `col p m E` `col p m A` `p \<noteq> m`] .
	have "col A E m" using collinearorder[OF `col m E A`] by blast
	have "parallel H F A G" using `parallel H F A G` .
	have "col A G B" using `col A G B` .
	have "G \<noteq> B" using betweennotequal[OF `bet A G B`] by blast
	have "B \<noteq> G" using inequalitysymmetric[OF `G \<noteq> B`] .
	have "parallel H F B G" using collinearparallel[OF `parallel H F A G` `col A G B` `B \<noteq> G`] .
	have "parallel B G H F" using parallelsymmetric[OF `parallel H F B G`] .
	have "parallel G B F H" using parallelflip[OF `parallel B G H F`] by blast
	have "\<not> (meets G B F H)" using parallel_f[OF `parallel G B F H`] by fastforce
	have "col G A B" using collinearorder[OF `col A G B`] by blast
	have "col F E H" using `col F E H` .
	have "F \<noteq> H" using `F \<noteq> H` .
	have "G \<noteq> A" using `G \<noteq> A` .
	have "E \<noteq> H" using `E \<noteq> H` .
	have "bet A m E" using collinearbetween[OF `col G A B` `col F E H` `G \<noteq> B` `F \<noteq> H` `G \<noteq> A` `E \<noteq> H` `\<not> (meets G B F H)` `bet G m H` `col A E m`] .
	have "cross A E G H" using cross_b[OF `bet A m E` `bet G m H`] .
	thus ?thesis by blast
qed

end