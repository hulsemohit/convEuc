theory rectangleparallelogram
	imports Axioms Definitions Theorems
begin

theorem rectangleparallelogram:
	assumes: `axioms`
		"rectangle A B C D"
	shows: "parallelogram A B C D"
proof -
	have "ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D" using rectangle_f[OF `axioms` `rectangle A B C D`] .
	have "ang_right D A B" using `ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D` by blast
	have "ang_right A B C" using `ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D` by blast
	have "ang_right C D A" using `ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D` by blast
	have "cross A C B D" using `ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D` by blast
	have "\<not> col D A B" using rightangleNC[OF `axioms` `ang_right D A B`] .
	have "\<not> col A B C" using rightangleNC[OF `axioms` `ang_right A B C`] .
	have "\<not> col C D A" using rightangleNC[OF `axioms` `ang_right C D A`] .
	obtain M where "bet A M C \<and> bet B M D" using cross_f[OF `axioms` `cross A C B D`] by blast
	have "bet A M C" using `bet A M C \<and> bet B M D` by blast
	have "bet B M D" using `bet A M C \<and> bet B M D` by blast
	have "\<not> (meets A B C D)"
	proof (rule ccontr)
		assume "meets A B C D"
		obtain P where "A \<noteq> B \<and> C \<noteq> D \<and> col A B P \<and> col C D P" using meet_f[OF `axioms` `meets A B C D`] by blast
		have "col A B P" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B P \<and> col C D P` by blast
		have "col C D P" using `A \<noteq> B \<and> C \<noteq> D \<and> col A B P \<and> col C D P` by blast
		have "\<not> (A = P)"
		proof (rule ccontr)
			assume "A = P"
			have "col C D A" using `col C D P` `A = P` by blast
			have "\<not> col C D A" using `\<not> col C D A` .
			show "False" using `\<not> col C D A` `col C D A` by blast
		qed
		hence "A \<noteq> P" by blast
		have "\<not> (D = P)"
		proof (rule ccontr)
			assume "D = P"
			have "col A B D" using `col A B P` `D = P` by blast
			have "col D A B" using collinearorder[OF `axioms` `col A B D`] by blast
			have "\<not> col D A B" using `\<not> col D A B` .
			show "False" using `\<not> col D A B` `col D A B` by blast
		qed
		hence "D \<noteq> P" by blast
		have "ang_right D A B" using `ang_right D A B` .
		have "ang_right C D A" using `ang_right C D A` .
		have "ang_right B A D" using n8_2[OF `axioms` `ang_right D A B`] .
		have "col B A P" using collinearorder[OF `axioms` `col A B P`] by blast
		have "P \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> P`] .
		have "ang_right P A D" using collinearright[OF `axioms` `ang_right B A D` `col B A P` `P \<noteq> A`] .
		have "P \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> P`] .
		have "ang_right P D A" using collinearright[OF `axioms` `ang_right C D A` `col C D P` `P \<noteq> D`] .
		have "ang_right A D P" using n8_2[OF `axioms` `ang_right P D A`] .
		have "\<not> (ang_right P A D)" using n8_7[OF `axioms` `ang_right A D P`] .
		show "False" using `\<not> (ang_right P A D)` `ang_right P A D` by blast
	qed
	hence "\<not> (meets A B C D)" by blast
	have "A \<noteq> B" using NCdistinct[OF `axioms` `\<not> col A B C`] by blast
	have "C \<noteq> D" using NCdistinct[OF `axioms` `\<not> col C D A`] by blast
	have "D \<noteq> C" using NCdistinct[OF `axioms` `\<not> col C D A`] by blast
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "col A B A" using collinear_b `axioms` `A = A` by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "col A B B" using collinear_b `axioms` `B = B` by blast
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "col C D C" using collinear_b `axioms` `C = C` by blast
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "col C D D" using collinear_b `axioms` `D = D` by blast
	have "bet A M C" using `bet A M C` .
	have "bet D M B" using betweennesssymmetryE[OF `axioms` `bet B M D`] .
	have "A \<noteq> B \<and> C \<noteq> D \<and> col A B A \<and> col A B B \<and> A \<noteq> B \<and> col C D D \<and> col C D C \<and> D \<noteq> C \<and> \<not> (meets A B C D) \<and> bet A M C \<and> bet D M B" using `A \<noteq> B` `C \<noteq> D` `col A B A` `col A B B` `A \<noteq> B` `col C D D` `col C D C` `D \<noteq> C` `\<not> (meets A B C D)` `bet A M C \<and> bet B M D` `bet D M B` by blast
	have "parallel A B C D" using parallel_b[OF `axioms` `A \<noteq> B` `C \<noteq> D` `col A B A` `col A B B` `A \<noteq> B` `col C D D` `col C D C` `D \<noteq> C` `\<not> (meets A B C D)` `bet A M C` `bet D M B`] .
	have "\<not> (meets A D B C)"
	proof (rule ccontr)
		assume "meets A D B C"
		obtain P where "A \<noteq> D \<and> B \<noteq> C \<and> col A D P \<and> col B C P" using meet_f[OF `axioms` `meets A D B C`] by blast
		have "col A D P" using `A \<noteq> D \<and> B \<noteq> C \<and> col A D P \<and> col B C P` by blast
		have "col B C P" using `A \<noteq> D \<and> B \<noteq> C \<and> col A D P \<and> col B C P` by blast
		have "\<not> (A = P)"
		proof (rule ccontr)
			assume "A = P"
			have "col B C A" using `col B C P` `A = P` by blast
			have "col A B C" using collinearorder[OF `axioms` `col B C A`] by blast
			have "\<not> col A B C" using `\<not> col A B C` .
			show "False" using `\<not> col A B C` `col A B C` by blast
		qed
		hence "A \<noteq> P" by blast
		have "\<not> (B = P)"
		proof (rule ccontr)
			assume "B = P"
			have "col A D B" using `col A D P` `B = P` by blast
			have "col D A B" using collinearorder[OF `axioms` `col A D B`] by blast
			have "\<not> col D A B" using `\<not> col D A B` .
			show "False" using `\<not> col D A B` `col D A B` by blast
		qed
		hence "B \<noteq> P" by blast
		have "ang_right D A B" using `ang_right D A B` .
		have "ang_right A B C" using `ang_right A B C` .
		have "P \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> P`] .
		have "col D A P" using collinearorder[OF `axioms` `col A D P`] by blast
		have "ang_right P A B" using collinearright[OF `axioms` `ang_right D A B` `col D A P` `P \<noteq> A`] .
		have "ang_right C B A" using n8_2[OF `axioms` `ang_right A B C`] .
		have "col C B P" using collinearorder[OF `axioms` `col B C P`] by blast
		have "P \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> P`] .
		have "ang_right P B A" using collinearright[OF `axioms` `ang_right C B A` `col C B P` `P \<noteq> B`] .
		have "ang_right B A P" using n8_2[OF `axioms` `ang_right P A B`] .
		have "\<not> (ang_right P B A)" using n8_7[OF `axioms` `ang_right B A P`] .
		show "False" using `\<not> (ang_right P B A)` `ang_right P B A` by blast
	qed
	hence "\<not> (meets A D B C)" by blast
	have "A \<noteq> D" using NCdistinct[OF `axioms` `\<not> col C D A`] by blast
	have "B \<noteq> C" using NCdistinct[OF `axioms` `\<not> col A B C`] by blast
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "col A D A" using collinear_b `axioms` `A = A` by blast
	have "col A D D" using collinear_b `axioms` `D = D` by blast
	have "col B C B" using collinear_b `axioms` `B = B` by blast
	have "col B C C" using collinear_b `axioms` `C = C` by blast
	have "A \<noteq> D" using `A \<noteq> D` .
	have "B \<noteq> C" using `B \<noteq> C` .
	have "\<not> (meets A D B C)" using `\<not> (meets A D B C)` .
	have "bet A M C" using `bet A M C` .
	have "parallel A D B C" using parallel_b[OF `axioms` `A \<noteq> D` `B \<noteq> C` `col A D A` `col A D D` `A \<noteq> D` `col B C B` `col B C C` `B \<noteq> C` `\<not> (meets A D B C)` `bet A M C` `bet B M D`] .
	have "parallelogram A B C D" using parallelogram_b[OF `axioms` `parallel A B C D` `parallel A D B C`] .
	thus ?thesis by blast
qed

end