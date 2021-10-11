theory lessthanadditive
	imports n3_6a n3_6b n3_7a Geometry betweennotequal congruenceflip congruencesymmetric congruencetransitive layoffunique lessthancongruence lessthancongruence2 outerconnectivity ray4 sumofparts trichotomy2
begin

theorem(in euclidean_geometry) lessthanadditive:
	assumes 
		"seg_lt A B C D"
		"bet A B E"
		"bet C D F"
		"seg_eq B E D F"
	shows "seg_lt A E C F"
proof -
	obtain b where "bet C b D \<and> seg_eq C b A B" using lessthan_f[OF `seg_lt A B C D`]  by  blast
	have "bet C b D" using `bet C b D \<and> seg_eq C b A B` by blast
	have "seg_eq C b A B" using `bet C b D \<and> seg_eq C b A B` by blast
	have "seg_eq A B C b" using congruencesymmetric[OF `seg_eq C b A B`] .
	have "C \<noteq> b" using betweennotequal[OF `bet C b D`] by blast
	have "B \<noteq> E" using betweennotequal[OF `bet A B E`] by blast
	obtain e where "bet C b e \<and> seg_eq b e B E" using extensionE[OF `C \<noteq> b` `B \<noteq> E`]  by  blast
	have "seg_eq b e B E" using `bet C b e \<and> seg_eq b e B E` by blast
	have "seg_eq B E b e" using congruencesymmetric[OF `seg_eq b e B E`] .
	have "bet C D F" using `bet C D F` .
	have "bet C b D" using `bet C b D` .
	have "bet C b F" using n3_6b[OF `bet C b D` `bet C D F`] .
	have "\<not> (bet b F e)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet b F e))"
hence "bet b F e" by blast
		have "seg_eq F D F D" using congruencereflexiveE.
		have "bet C b D" using `bet C b D` .
		have "bet C D F" using `bet C D F` .
		have "bet b D F" using n3_6a[OF `bet C b D` `bet C D F`] .
		have "bet F D b" using betweennesssymmetryE[OF `bet b D F`] .
		have "seg_lt F D F b" using lessthan_b[OF `bet F D b` `seg_eq F D F D`] .
		have "seg_eq F b b F" using equalityreverseE.
		have "seg_lt F D b F" using lessthancongruence[OF `seg_lt F D F b` `seg_eq F b b F`] .
		have "seg_eq F D D F" using equalityreverseE.
		have "seg_lt D F b F" using lessthancongruence2[OF `seg_lt F D b F` `seg_eq F D D F`] .
		have "seg_eq b e B E" using `seg_eq b e B E` .
		have "seg_eq B E D F" using `seg_eq B E D F` .
		have "seg_eq b e D F" using congruencetransitive[OF `seg_eq b e B E` `seg_eq B E D F`] .
		have "seg_eq D F b e" using congruencesymmetric[OF `seg_eq b e D F`] .
		have "seg_lt b e b F" using lessthancongruence2[OF `seg_lt D F b F` `seg_eq D F b e`] .
		obtain q where "bet b q F \<and> seg_eq b q b e" using lessthan_f[OF `seg_lt b e b F`]  by  blast
		have "bet b q F" using `bet b q F \<and> seg_eq b q b e` by blast
		have "seg_eq b q b e" using `bet b q F \<and> seg_eq b q b e` by blast
		have "b \<noteq> F" using betweennotequal[OF `bet C b F`] by blast
		have "ray_on b F q" using ray4 `bet b q F \<and> seg_eq b q b e` `b \<noteq> F` by blast
		have "ray_on b F e" using ray4 `bet b F e` `b \<noteq> F` by blast
		have "q = e" using layoffunique[OF `ray_on b F q` `ray_on b F e` `seg_eq b q b e`] .
		have "bet b e F" using `bet b q F` `q = e` by blast
		have "bet F e F" using n3_6a[OF `bet b F e` `bet b e F`] .
		have "\<not> (bet F e F)" using betweennessidentityE.
		show "False" using `\<not> (bet F e F)` `bet F e F` by blast
	qed
	hence "\<not> (bet b F e)" by blast
	have "\<not> (F = e)"
	proof (rule ccontr)
		assume "\<not> (F \<noteq> e)"
		hence "F = e" by blast
		have "seg_eq b e B E" using `seg_eq b e B E` .
		have "seg_eq b F B E" using `seg_eq b e B E` `F = e` by blast
		have "bet C b D" using `bet C b D` .
		have "bet C D F" using `bet C D F` .
		have "bet b D F" using n3_6a[OF `bet C b D` `bet C D F`] .
		have "bet F D b" using betweennesssymmetryE[OF `bet b D F`] .
		have "seg_eq F D F D" using congruencereflexiveE.
		have "seg_lt F D F b" using lessthan_b[OF `bet F D b` `seg_eq F D F D`] .
		have "seg_eq F b b F" using equalityreverseE.
		have "seg_lt F D b F" using lessthancongruence[OF `seg_lt F D F b` `seg_eq F b b F`] .
		have "seg_eq D F B E" using congruencesymmetric[OF `seg_eq B E D F`] .
		have "seg_eq F D B E" using congruenceflip[OF `seg_eq D F B E`] by blast
		have "seg_lt B E b F" using lessthancongruence2[OF `seg_lt F D b F` `seg_eq F D B E`] .
		have "seg_eq b F b e" using congruencetransitive[OF `seg_eq b F B E` `seg_eq B E b e`] .
		have "seg_lt B E b e" using lessthancongruence[OF `seg_lt B E b F` `seg_eq b F b e`] .
		have "seg_eq b e B E" using `seg_eq b e B E` .
		have "seg_lt B E B E" using lessthancongruence[OF `seg_lt B E b F` `seg_eq b F B E`] .
		have "\<not> (seg_lt B E B E)" using trichotomy2[OF `seg_lt B E B E`] .
		show "False" using `\<not> (seg_lt B E B E)` `seg_lt B E B E` by blast
	qed
	hence "F \<noteq> e" by blast
	have "bet C b e" using `bet C b e \<and> seg_eq b e B E` by blast
	have "bet C b F" using `bet C b F` .
	have "\<not> (\<not> (bet b e F))"
	proof (rule ccontr)
		assume "\<not> (\<not> (\<not> (bet b e F)))"
hence "\<not> (bet b e F)" by blast
		have "\<not> (bet b F e)" using `\<not> (bet b F e)` .
		have "F = e" using outerconnectivity[OF `bet C b F` `bet C b e` `\<not> (bet b F e)` `\<not> (bet b e F)`] .
		have "F \<noteq> e" using `F \<noteq> e` .
		show "False" using `F \<noteq> e` `F = e` by blast
	qed
	hence "bet b e F" by blast
	have "bet C b e" using `bet C b e` .
	have "bet C e F" using n3_7a[OF `bet C b e` `bet b e F`] .
	have "seg_eq A B C b" using `seg_eq A B C b` .
	have "seg_eq B E b e" using `seg_eq B E b e` .
	have "seg_eq A E C e" using sumofparts[OF `seg_eq A B C b` `seg_eq B E b e` `bet A B E` `bet C b e`] .
	have "seg_eq C e A E" using congruencesymmetric[OF `seg_eq A E C e`] .
	have "seg_lt A E C F" using lessthan_b[OF `bet C e F` `seg_eq C e A E`] .
	thus ?thesis by blast
qed

end