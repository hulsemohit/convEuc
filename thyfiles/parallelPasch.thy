theory parallelPasch
	imports Geometry NCorder betweennotequal collinear4 collinearbetween collinearorder inequalitysymmetric parallelNC paralleldef2B parallelsymmetric planeseparation samesidesymmetric
begin

theorem(in euclidean_geometry) parallelPasch:
	assumes 
		"parallelogram A B C D"
		"bet A D E"
	shows "\<exists> H. bet B H E \<and> bet C H D"
proof -
	have "parallel A B C D" using parallelogram_f[OF `parallelogram A B C D`] by blast
	have "parallel A D B C" using parallelogram_f[OF `parallelogram A B C D`] by blast
	have "parallel C D A B" using parallelsymmetric[OF `parallel A B C D`] .
	have "tarski_parallel C D A B" using paralleldef2B[OF `parallel C D A B`] .
	have "same_side A B C D" using tarski_parallel_f[OF `tarski_parallel C D A B`] by blast
	have "same_side B A C D" using samesidesymmetric[OF `same_side A B C D`] by blast
	have "D = D" using equalityreflexiveE.
	have "A \<noteq> D" using betweennotequal[OF `bet A D E`] by blast
	have "col A D D" using collinear_b `D = D` by blast
	have "col A D E" using collinear_b `bet A D E` by blast
	have "col D D E" using collinear4[OF `col A D D` `col A D E` `A \<noteq> D`] .
	have "col E D D" using collinearorder[OF `col D D E`] by blast
	have "col C D D" using collinear_b `D = D` by blast
	have "\<not> col A C D" using parallelNC[OF `parallel A B C D`] by blast
	have "\<not> col C D A" using NCorder[OF `\<not> col A C D`] by blast
	have "bet A D E \<and> col C D D \<and> \<not> col C D A" using `bet A D E` `col C D D` `\<not> col C D A` by blast
	have "oppo_side A C D E" using oppositeside_b[OF `bet A D E` `col C D D` `\<not> col C D A`] .
	have "oppo_side B C D E" using planeseparation[OF `same_side B A C D` `oppo_side A C D E`] .
	obtain H where "bet B H E \<and> col C D H \<and> \<not> col C D B" using oppositeside_f[OF `oppo_side B C D E`]  by  blast
	have "bet B H E" using `bet B H E \<and> col C D H \<and> \<not> col C D B` by blast
	have "col C D H" using `bet B H E \<and> col C D H \<and> \<not> col C D B` by blast
	have "bet E H B" using betweennesssymmetryE[OF `bet B H E`] .
	have "col D C H" using collinearorder[OF `col C D H`] by blast
	have "parallel A D B C" using `parallel A D B C` .
	have "A \<noteq> D" using parallel_f[OF `parallel A D B C`] by fastforce
	have "\<not> (meets A D B C)" using parallel_f[OF `parallel A D B C`] by fastforce
	have "\<not> (meets E D C B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (meets E D C B))"
hence "meets E D C B" by blast
		obtain p where "E \<noteq> D \<and> C \<noteq> B \<and> col E D p \<and> col C B p" using meet_f[OF `meets E D C B`]  by  blast
		have "E \<noteq> D" using `E \<noteq> D \<and> C \<noteq> B \<and> col E D p \<and> col C B p` by blast
		have "C \<noteq> B" using `E \<noteq> D \<and> C \<noteq> B \<and> col E D p \<and> col C B p` by blast
		have "B \<noteq> C" using inequalitysymmetric[OF `C \<noteq> B`] .
		have "col E D p" using `E \<noteq> D \<and> C \<noteq> B \<and> col E D p \<and> col C B p` by blast
		have "col C B p" using `E \<noteq> D \<and> C \<noteq> B \<and> col E D p \<and> col C B p` by blast
		have "col B C p" using collinearorder[OF `col C B p`] by blast
		have "col A D E" using `col A D E` .
		have "col E D A" using collinearorder[OF `col A D E`] by blast
		have "col D A p" using collinear4[OF `col E D A` `col E D p` `E \<noteq> D`] .
		have "col A D p" using collinearorder[OF `col D A p`] by blast
		have "A \<noteq> D \<and> B \<noteq> C \<and> col A D p \<and> col B C p" using `A \<noteq> D` `B \<noteq> C` `col A D p` `col B C p` by blast
		have "meets A D B C" using meet_b[OF `A \<noteq> D` `B \<noteq> C` `col A D p` `col B C p`] .
		show "False" using `meets A D B C` `\<not> (meets A D B C)` by blast
	qed
	hence "\<not> (meets E D C B)" by blast
	have "C = C" using equalityreflexiveE.
	have "D \<noteq> E" using betweennotequal[OF `bet A D E`] by blast
	have "E \<noteq> D" using inequalitysymmetric[OF `D \<noteq> E`] .
	have "B \<noteq> C" using parallel_f[OF `parallel A D B C`] by fastforce
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	have "col C C B" using collinear_b `C = C` by blast
	have "col E D D" using `col E D D` .
	have "bet D H C" using collinearbetween[OF `col E D D` `col C C B` `E \<noteq> D` `C \<noteq> B` `E \<noteq> D` `C \<noteq> B` `\<not> (meets E D C B)` `bet E H B` `col D C H`] .
	have "bet C H D" using betweennesssymmetryE[OF `bet D H C`] .
	have "bet B H E \<and> bet C H D" using `bet B H E \<and> col C D H \<and> \<not> col C D B` `bet C H D` by blast
	thus ?thesis by blast
qed

end