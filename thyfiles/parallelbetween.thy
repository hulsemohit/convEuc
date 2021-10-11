theory parallelbetween
	imports Geometry NCdistinct NChelper NCorder collinearorder parallelNC
begin

theorem(in euclidean_geometry) parallelbetween:
	assumes 
		"bet H B K"
		"parallel M B H L"
		"col L M K"
	shows "bet L M K"
proof -
	have "\<not> (meets M B H L)" using parallel_f[OF `parallel M B H L`] by fastforce
	have "\<not> col M B H" using parallelNC[OF `parallel M B H L`] by blast
	have "\<not> col M H L" using parallelNC[OF `parallel M B H L`] by blast
	have "M \<noteq> B" using NCdistinct[OF `\<not> col M B H`] by blast
	have "H \<noteq> L" using NCdistinct[OF `\<not> col M H L`] by blast
	have "\<not> col M L H" using NCorder[OF `\<not> col M H L`] by blast
	have "col M L K" using collinearorder[OF `col L M K`] by blast
	have "col H B K" using collinear_b `bet H B K` by blast
	have "M = M" using equalityreflexiveE.
	have "L = L" using equalityreflexiveE.
	have "B = B" using equalityreflexiveE.
	have "H = H" using equalityreflexiveE.
	have "\<not> (M = K)"
	proof (rule ccontr)
		assume "\<not> (M \<noteq> K)"
		hence "M = K" by blast
		have "col H B M" using `col H B K` `M = K` by blast
		have "col M B H" using collinearorder[OF `col H B M`] by blast
		have "col H L H" using collinear_b `H = H` by blast
		have "meets M B H L" using meet_b[OF `M \<noteq> B` `H \<noteq> L` `col M B H` `col H L H`] .
		show "False" using `meets M B H L` `\<not> (meets M B H L)` by blast
	qed
	hence "M \<noteq> K" by blast
	have "\<not> col M L H" using NCorder[OF `\<not> col M H L`] by blast
	have "col M L M" using collinear_b `M = M` by blast
	have "\<not> col M K H" using NChelper[OF `\<not> col M L H` `col M L M` `col M L K` `M \<noteq> K`] .
	have "\<not> col H M K" using NCorder[OF `\<not> col M K H`] by blast
	have "L = M \<or> L = K \<or> M = K \<or> bet M L K \<or> bet L M K \<or> bet L K M" using collinear_f[OF `col L M K`] .
	consider "L = M"|"L = K"|"M = K"|"bet M L K"|"bet L M K"|"bet L K M" using `L = M \<or> L = K \<or> M = K \<or> bet M L K \<or> bet L M K \<or> bet L K M`  by blast
	hence "bet L M K"
	proof (cases)
		assume "L = M"
		have "\<not> (\<not> (bet L M K))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet L M K)))"
hence "\<not> (bet L M K)" by blast
			have "col M B M" using collinear_b `M = M` by blast
			have "col H L L" using collinear_b `L = L` by blast
			have "col H L M" using `col H L L` `L = M` by blast
			have "meets M B H L" using meet_b[OF `M \<noteq> B` `H \<noteq> L` `col M B M` `col H L M`] .
			show "False" using `meets M B H L` `\<not> (meets M B H L)` by blast
		qed
		hence "bet L M K" by blast
		thus ?thesis by blast
	next
		assume "L = K"
		have "\<not> (\<not> (bet L M K))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet L M K)))"
hence "\<not> (bet L M K)" by blast
			have "col H B L" using `col H B K` `L = K` by blast
			have "col H L B" using collinearorder[OF `col H B L`] by blast
			have "col M B B" using collinear_b `B = B` by blast
			have "meets M B H L" using meet_b[OF `M \<noteq> B` `H \<noteq> L` `col M B B` `col H L B`] .
			show "False" using `meets M B H L` `\<not> (meets M B H L)` by blast
		qed
		hence "bet L M K" by blast
		thus ?thesis by blast
	next
		assume "M = K"
		have "\<not> (\<not> (bet L M K))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet L M K)))"
hence "\<not> (bet L M K)" by blast
			have "M \<noteq> K" using `M \<noteq> K` .
			show "False" using `M \<noteq> K` `M = K` by blast
		qed
		hence "bet L M K" by blast
		thus ?thesis by blast
	next
		assume "bet M L K"
		have "\<not> (\<not> (bet L M K))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet L M K)))"
hence "\<not> (bet L M K)" by blast
			have "\<not> col H K M" using NCorder[OF `\<not> col H M K`] by blast
			obtain E where "bet H E L \<and> bet M E B" using Pasch_innerE[OF `bet H B K` `bet M L K` `\<not> col H K M`]  by  blast
			have "bet H E L" using `bet H E L \<and> bet M E B` by blast
			have "bet M E B" using `bet H E L \<and> bet M E B` by blast
			have "col H E L" using collinear_b `bet H E L \<and> bet M E B` by blast
			have "col M E B" using collinear_b `bet H E L \<and> bet M E B` by blast
			have "col H L E" using collinearorder[OF `col H E L`] by blast
			have "col M B E" using collinearorder[OF `col M E B`] by blast
			have "meets M B H L" using meet_b[OF `M \<noteq> B` `H \<noteq> L` `col M B E` `col H L E`] .
			show "False" using `meets M B H L` `\<not> (meets M B H L)` by blast
		qed
		hence "bet L M K" by blast
		thus ?thesis by blast
	next
		assume "bet L M K"
		have "bet L M K" using `bet L M K` .
		thus ?thesis by blast
	next
		assume "bet L K M"
		have "\<not> (\<not> (bet L M K))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (bet L M K)))"
hence "\<not> (bet L M K)" by blast
			have "\<not> col M L H" using `\<not> col M L H` .
			have "bet M K L" using betweennesssymmetryE[OF `bet L K M`] .
			obtain E where "bet H E L \<and> bet M B E" using Pasch_outerE[OF `bet H B K` `bet M K L` `\<not> col M L H`]  by  blast
			have "bet H E L" using `bet H E L \<and> bet M B E` by blast
			have "bet M B E" using `bet H E L \<and> bet M B E` by blast
			have "col H E L" using collinear_b `bet H E L \<and> bet M B E` by blast
			have "col M B E" using collinear_b `bet H E L \<and> bet M B E` by blast
			have "col H L E" using collinearorder[OF `col H E L`] by blast
			have "meets M B H L" using meet_b[OF `M \<noteq> B` `H \<noteq> L` `col M B E` `col H L E`] .
			show "False" using `meets M B H L` `\<not> (meets M B H L)` by blast
		qed
		hence "bet L M K" by blast
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end