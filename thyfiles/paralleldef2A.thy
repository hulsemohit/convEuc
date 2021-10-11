theory paralleldef2A
	imports Geometry betweennotequal collinear4 collinearorder inequalitysymmetric
begin

theorem(in euclidean_geometry) paralleldef2A:
	assumes 
		"tarski_parallel A B C D"
	shows "parallel A B C D"
proof -
	have "A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B" using tarski_parallel_f[OF `tarski_parallel A B C D`] .
	have "A \<noteq> B" using `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` by blast
	have "C \<noteq> D" using `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` by blast
	have "\<not> (meets A B C D)" using `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` by blast
	have "same_side C D A B" using `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` by blast
	obtain a b e where "col A B a \<and> col A B b \<and> bet C a e \<and> bet D b e \<and> \<not> col A B C \<and> \<not> col A B D" using sameside_f[OF `same_side C D A B`]  by  blast
	have "col A B a" using `col A B a \<and> col A B b \<and> bet C a e \<and> bet D b e \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col A B b" using `col A B a \<and> col A B b \<and> bet C a e \<and> bet D b e \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "bet C a e" using `col A B a \<and> col A B b \<and> bet C a e \<and> bet D b e \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "bet D b e" using `col A B a \<and> col A B b \<and> bet C a e \<and> bet D b e \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col C a e" using collinear_b `col A B a \<and> col A B b \<and> bet C a e \<and> bet D b e \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "col D b e" using collinear_b `col A B a \<and> col A B b \<and> bet C a e \<and> bet D b e \<and> \<not> col A B C \<and> \<not> col A B D` by blast
	have "a \<noteq> e" using betweennotequal[OF `bet C a e`] by blast
	have "C \<noteq> e" using betweennotequal[OF `bet C a e`] by blast
	have "D \<noteq> e" using betweennotequal[OF `bet D b e`] by blast
	have "e \<noteq> D" using inequalitysymmetric[OF `D \<noteq> e`] .
	have "\<not> (a = b)"
	proof (rule ccontr)
		assume "\<not> (a \<noteq> b)"
		hence "a = b" by blast
		have "col C a e" using `col C a e` .
		have "col D a e" using `col D b e` `a = b` by blast
		have "col a e C" using collinearorder[OF `col C a e`] by blast
		have "col a e D" using collinearorder[OF `col D a e`] by blast
		have "col e C D" using collinear4[OF `col a e C` `col a e D` `a \<noteq> e`] .
		have "col e D C" using collinearorder[OF `col e C D`] by blast
		have "col e D b" using collinearorder[OF `col D b e`] by blast
		have "col D C b" using collinear4[OF `col e D C` `col e D b` `e \<noteq> D`] .
		have "col C D b" using collinearorder[OF `col D C b`] by blast
		have "col A B b" using `col A B b` .
		have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B b` `col C D b`] .
		have "\<not> (meets A B C D)" using `\<not> (meets A B C D)` .
		show "False" using `\<not> (meets A B C D)` `meets A B C D` by blast
	qed
	hence "a \<noteq> b" by blast
	have "\<not> (col C e D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col C e D))"
hence "col C e D" by blast
		have "col C e a" using collinearorder[OF `col C a e`] by blast
		have "col e D a" using collinear4[OF `col C e D` `col C e a` `C \<noteq> e`] .
		have "col e D C" using collinearorder[OF `col C e D`] by blast
		have "col D C a" using collinear4[OF `col e D C` `col e D a` `e \<noteq> D`] .
		have "col C D a" using collinearorder[OF `col D C a`] by blast
		have "col A B a" using `col A B a` .
		have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B a` `col C D a`] .
		have "\<not> (meets A B C D)" using `\<not> (meets A B C D)` .
		show "False" using `\<not> (meets A B C D)` `meets A B C D` by blast
	qed
	hence "\<not> col C e D" by blast
	have "bet C a e" using `bet C a e` .
	have "bet D b e" using `bet D b e` .
	obtain M where "bet C M b \<and> bet D M a" using Pasch_innerE[OF `bet C a e` `bet D b e` `\<not> col C e D`]  by  blast
	have "bet C M b" using `bet C M b \<and> bet D M a` by blast
	have "bet D M a" using `bet C M b \<and> bet D M a` by blast
	have "bet a M D" using betweennesssymmetryE[OF `bet D M a`] .
	have "C = C" using equalityreflexiveE.
	have "col C D C" using collinear_b `C = C` by blast
	have "D = D" using equalityreflexiveE.
	have "col C D D" using collinear_b `D = D` by blast
	have "A \<noteq> B \<and> C \<noteq> D \<and> col A B a \<and> col A B b \<and> a \<noteq> b \<and> col C D C \<and> col C D D \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> bet a M D \<and> bet C M b" using `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` `col A B a \<and> col A B b \<and> bet C a e \<and> bet D b e \<and> \<not> col A B C \<and> \<not> col A B D` `col A B a \<and> col A B b \<and> bet C a e \<and> bet D b e \<and> \<not> col A B C \<and> \<not> col A B D` `a \<noteq> b` `col C D C` `col C D D` `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` `A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B` `bet a M D` `bet C M b \<and> bet D M a` by blast
	have "parallel A B C D" using parallel_b[OF `A \<noteq> B` `C \<noteq> D` `col A B a` `col A B b` `a \<noteq> b` `col C D C` `col C D D` `C \<noteq> D` `\<not> (meets A B C D)` `bet a M D` `bet C M b`] .
	thus ?thesis by blast
qed

end