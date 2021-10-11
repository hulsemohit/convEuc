theory trapezoiddiagonals
	imports Geometry betweennotequal collinear4 collinearorder congruenceflip diagonalsbisect inequalitysymmetric
begin

theorem(in euclidean_geometry) trapezoiddiagonals:
	assumes 
		"parallelogram A B C D"
		"bet A E D"
	shows "\<exists> H. bet B H D \<and> bet C H E"
proof -
	have "parallel A B C D" using parallelogram_f[OF `parallelogram A B C D`] by blast
	have "parallel A D B C" using parallelogram_f[OF `parallelogram A B C D`] by blast
	have "\<not> (meets A B C D)" using parallel_f[OF `parallel A B C D`] by fastforce
	have "A \<noteq> B" using parallel_f[OF `parallel A B C D`] by fastforce
	have "C \<noteq> D" using parallel_f[OF `parallel A B C D`] by fastforce
	obtain M where "midpoint A M C \<and> midpoint B M D" using diagonalsbisect[OF `parallelogram A B C D`]  by  blast
	have "midpoint A M C" using `midpoint A M C \<and> midpoint B M D` by blast
	have "midpoint B M D" using `midpoint A M C \<and> midpoint B M D` by blast
	have "bet A M C" using midpoint_f[OF `midpoint A M C`] by blast
	have "seg_eq A M M C" using midpoint_f[OF `midpoint A M C`] by blast
	have "bet B M D" using midpoint_f[OF `midpoint B M D`] by blast
	have "seg_eq B M M D" using midpoint_f[OF `midpoint B M D`] by blast
	have "seg_eq B M D M" using congruenceflip[OF `seg_eq B M M D`] by blast
	have "B = B" using equalityreflexiveE.
	have "\<not> (col B D C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B D C))"
hence "col B D C" by blast
		have "col C D B" using collinearorder[OF `col B D C`] by blast
		have "col A B B" using collinear_b `B = B` by blast
		have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B B` `col C D B`] .
		have "\<not> (meets A B C D)" using `\<not> (meets A B C D)` .
		show "False" using `\<not> (meets A B C D)` `meets A B C D` by blast
	qed
	hence "\<not> col B D C" by blast
	have "seg_eq M A M C" using congruenceflip[OF `seg_eq A M M C`] by blast
	obtain P where "bet B E P \<and> bet C D P" using Euclid5E[OF `bet A M C` `bet B M D` `bet A E D` `seg_eq B M D M` `seg_eq M A M C`]  by  blast
	have "bet B E P" using `bet B E P \<and> bet C D P` by blast
	have "bet C D P" using `bet B E P \<and> bet C D P` by blast
	have "\<not> (col B P C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B P C))"
hence "col B P C" by blast
		have "col P C B" using collinearorder[OF `col B P C`] by blast
		have "col C D P" using collinear_b `bet B E P \<and> bet C D P` by blast
		have "col P C D" using collinearorder[OF `col C D P`] by blast
		have "C \<noteq> P" using betweennotequal[OF `bet C D P`] by blast
		have "P \<noteq> C" using inequalitysymmetric[OF `C \<noteq> P`] .
		have "col C B D" using collinear4[OF `col P C B` `col P C D` `P \<noteq> C`] .
		have "col C D B" using collinearorder[OF `col C B D`] by blast
		have "col A B B" using collinear_b `B = B` by blast
		have "meets A B C D" using meet_b[OF `A \<noteq> B` `C \<noteq> D` `col A B B` `col C D B`] .
		have "\<not> (meets A B C D)" using `\<not> (meets A B C D)` .
		show "False" using `\<not> (meets A B C D)` `meets A B C D` by blast
	qed
	hence "\<not> col B P C" by blast
	obtain H where "bet B H D \<and> bet C H E" using Pasch_innerE[OF `bet B E P` `bet C D P` `\<not> col B P C`]  by  blast
	thus ?thesis by blast
qed

end