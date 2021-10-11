theory Playfairhelper2
	imports n3_6b Geometry NChelper NCorder Playfairhelper betweennotequal collinear4 collinearbetween collinearorder collinearparallel crisscross inequalitysymmetric parallelNC parallelflip parallelsymmetric
begin

theorem(in euclidean_geometry) Playfairhelper2:
	assumes 
		"parallel A B C D"
		"parallel A B C E"
		"cross A D B C"
	shows "col C D E"
proof -
	have "A \<noteq> B" using parallel_f[OF `parallel A B C D`] by fastforce
	have "\<not> (\<not> (cross A E B C \<or> cross A C E B))"
	proof (rule ccontr)
		assume "\<not> (\<not> (\<not> (cross A E B C \<or> cross A C E B)))"
hence "\<not> (cross A E B C \<or> cross A C E B)" by blast
		have "\<not> (cross A E B C) \<and> \<not> (cross A C E B)" using `\<not> (cross A E B C \<or> cross A C E B)` by blast
		have "\<not> (cross A E B C)" using `\<not> (cross A E B C) \<and> \<not> (cross A C E B)` by blast
		have "\<not> (cross A C E B)" using `\<not> (cross A E B C) \<and> \<not> (cross A C E B)` by blast
		have "parallel A B E C" using parallelflip[OF `parallel A B C E`] by blast
		have "cross A C E B" using crisscross[OF `parallel A B E C` `\<not> (cross A E B C)`] .
		show "False" using `cross A C E B` `\<not> (cross A E B C) \<and> \<not> (cross A C E B)` by blast
	qed
	hence "cross A E B C \<or> cross A C E B" by blast
	obtain M where "bet A M D \<and> bet B M C" using cross_f[OF `cross A D B C`]  by  blast
	have "bet B M C" using `bet A M D \<and> bet B M C` by blast
	consider "cross A E B C"|"cross A C E B" using `\<not> (\<not> (cross A E B C \<or> cross A C E B))`  by blast
	hence "col C D E"
	proof (cases)
		assume "cross A E B C"
		have "col C D E" using Playfairhelper[OF `parallel A B C D` `parallel A B C E` `cross A D B C` `cross A E B C`] .
		thus ?thesis by blast
	next
		assume "cross A C E B"
		obtain m where "bet A m C \<and> bet E m B" using cross_f[OF `cross A C E B`]  by  blast
		have "bet A m C" using `bet A m C \<and> bet E m B` by blast
		have "bet E m B" using `bet A m C \<and> bet E m B` by blast
		have "C \<noteq> E" using parallel_f[OF `parallel A B C E`] by fastforce
		have "E \<noteq> C" using inequalitysymmetric[OF `C \<noteq> E`] .
		obtain e where "bet E C e \<and> seg_eq C e E C" using extensionE[OF `E \<noteq> C` `E \<noteq> C`]  by  blast
		have "bet E C e" using `bet E C e \<and> seg_eq C e E C` by blast
		have "col E C e" using collinear_b `bet E C e \<and> seg_eq C e E C` by blast
		have "C \<noteq> e" using betweennotequal[OF `bet E C e`] by blast
		have "e \<noteq> C" using inequalitysymmetric[OF `C \<noteq> e`] .
		have "parallel A B E C" using parallelflip[OF `parallel A B C E`] by blast
		have "parallel A B e C" using collinearparallel[OF `parallel A B E C` `col E C e` `e \<noteq> C`] .
		have "parallel A B C e" using parallelflip[OF `parallel A B e C`] by blast
		have "\<not> col A B C" using parallelNC[OF `parallel A B C D`] by blast
		have "\<not> col B C A" using NCorder[OF `\<not> col A B C`] by blast
		obtain H where "bet B H m \<and> bet A H M" using Pasch_innerE[OF `bet B M C` `bet A m C` `\<not> col B C A`]  by  blast
		have "\<not> col A E C" using parallelNC[OF `parallel A B E C`] by blast
		have "col E C e" using collinear_b `bet E C e \<and> seg_eq C e E C` by blast
		have "col C E e" using collinearorder[OF `col E C e`] by blast
		have "\<not> col C E A" using NCorder[OF `\<not> col A E C`] by blast
		have "E = E" using equalityreflexiveE.
		have "col C E E" using collinear_b `E = E` by blast
		have "E \<noteq> e" using betweennotequal[OF `bet E C e`] by blast
		have "\<not> col E e A" using NChelper[OF `\<not> col C E A` `col C E E` `col C E e` `E \<noteq> e`] .
		have "bet A m C" using `bet A m C` .
		have "bet E C e" using `bet E C e` .
		obtain F where "bet A F e \<and> bet E m F" using Pasch_outerE[OF `bet A m C` `bet E C e` `\<not> col E e A`]  by  blast
		have "bet A F e" using `bet A F e \<and> bet E m F` by blast
		have "bet E m F" using `bet A F e \<and> bet E m F` by blast
		have "bet e F A" using betweennesssymmetryE[OF `bet A F e`] .
		have "col E m F" using collinear_b `bet A F e \<and> bet E m F` by blast
		have "col E m B" using collinear_b `bet A m C \<and> bet E m B` by blast
		have "col m E F" using collinearorder[OF `col E m F`] by blast
		have "col m E B" using collinearorder[OF `col E m B`] by blast
		have "E \<noteq> m" using betweennotequal[OF `bet E m B`] by blast
		have "m \<noteq> E" using inequalitysymmetric[OF `E \<noteq> m`] .
		have "col E F B" using collinear4[OF `col m E F` `col m E B` `m \<noteq> E`] .
		have "col E B F" using collinearorder[OF `col E F B`] by blast
		have "e \<noteq> E" using inequalitysymmetric[OF `E \<noteq> e`] .
		have "bet e F A" using `bet e F A` .
		have "E = E" using equalityreflexiveE.
		have "col e E E" using collinear_b `E = E` by blast
		have "B = B" using equalityreflexiveE.
		have "col B B A" using collinear_b `B = B` by blast
		have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
		have "parallel A B E C" using `parallel A B E C` .
		have "parallel A B C E" using parallelflip[OF `parallel A B E C`] by blast
		have "col E C e" using `col E C e` .
		have "col C E e" using collinearorder[OF `col E C e`] by blast
		have "E \<noteq> e" using `E \<noteq> e` .
		have "parallel A B e E" using collinearparallel[OF `parallel A B C E` `col C E e` `e \<noteq> E`] .
		have "parallel e E A B" using parallelsymmetric[OF `parallel A B e E`] .
		have "parallel e E B A" using parallelflip[OF `parallel e E A B`] by blast
		have "\<not> (meets e E B A)" using parallel_f[OF `parallel e E B A`] by fastforce
		have "bet E F B" using collinearbetween[OF `col e E E` `col B B A` `e \<noteq> E` `B \<noteq> A` `e \<noteq> E` `B \<noteq> A` `\<not> (meets e E B A)` `bet e F A` `col E B F`] .
		have "bet B F E" using betweennesssymmetryE[OF `bet E F B`] .
		have "bet e C E" using betweennesssymmetryE[OF `bet E C e`] .
		have "\<not> col B E C" using parallelNC[OF `parallel A B E C`] by blast
		have "\<not> col E C B" using NCorder[OF `\<not> col B E C`] by blast
		have "col E C e" using collinear_b `bet E C e \<and> seg_eq C e E C` by blast
		have "E = E" using equalityreflexiveE.
		have "col E C E" using collinear_b `E = E` by blast
		have "\<not> col E e B" using NChelper[OF `\<not> col E C B` `col E C E` `col E C e` `E \<noteq> e`] .
		have "\<not> col B E e" using NCorder[OF `\<not> col E e B`] by blast
		obtain K where "bet B K C \<and> bet e K F" using Pasch_innerE[OF `bet B F E` `bet e C E` `\<not> col B E e`]  by  blast
		have "bet B K C" using `bet B K C \<and> bet e K F` by blast
		have "bet e K F" using `bet B K C \<and> bet e K F` by blast
		have "bet e F A" using betweennesssymmetryE[OF `bet A F e`] .
		have "bet e K A" using n3_6b[OF `bet e K F` `bet e F A`] .
		have "bet A K e" using betweennesssymmetryE[OF `bet e K A`] .
		have "bet A K e" using `bet A K e` .
		have "bet B K C" using `bet B K C` .
		have "bet A K e \<and> bet B K C" using `bet A K e` `bet B K C \<and> bet e K F` by blast
		have "cross A e B C" using cross_b[OF `bet A K e` `bet B K C`] .
		have "col C D e" using Playfairhelper[OF `parallel A B C D` `parallel A B C e` `cross A D B C` `cross A e B C`] .
		have "col e C D" using collinearorder[OF `col C D e`] by blast
		have "col e C E" using collinearorder[OF `col C E e`] by blast
		have "C \<noteq> e" using betweennotequal[OF `bet E C e`] by blast
		have "e \<noteq> C" using inequalitysymmetric[OF `C \<noteq> e`] .
		have "col C D E" using collinear4[OF `col e C D` `col e C E` `e \<noteq> C`] .
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end