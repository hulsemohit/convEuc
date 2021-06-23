theory Prop47A
	imports n8_2 n8_3 n8_7 Geometry NCdistinct NCorder Playfair Prop12 Prop29C Prop34 altitudeofrighttriangle betweennesspreserved betweennotequal collinear4 collinearorder collinearparallel collinearright equaltorightisright erectedperpendicularunique inequalitysymmetric nullsegment3 parallelNC paralleldef2B parallelflip parallelsymmetric planeseparation ray4 ray5 rayimpliescollinear rightangleNC sameside2 samesideflip samesidesymmetric squareparallelogram twoperpsparallel
begin

theorem Prop47A:
	assumes "axioms"
		"triangle A B C"
		"ang_right B A C"
		"square B C E D"
		"oppo_side D C B A"
	shows "\<exists> L M. parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A"
proof -
	obtain N where "bet D N A \<and> col C B N \<and> \<not> col C B D" using oppositeside_f[OF `axioms` `oppo_side D C B A`]  by  blast
	have "bet D N A" using `bet D N A \<and> col C B N \<and> \<not> col C B D` by blast
	have "col C B N" using `bet D N A \<and> col C B N \<and> \<not> col C B D` by blast
	have "ang_right C A B" using n8_2[OF `axioms` `ang_right B A C`] .
	have "\<not> col C A B" using rightangleNC[OF `axioms` `ang_right C A B`] .
	have "A \<noteq> B" using NCdistinct[OF `axioms` `\<not> col C A B`] by blast
	have "\<not> col A B C" using triangle_f[OF `axioms` `triangle A B C`] .
	have "B \<noteq> C" using NCdistinct[OF `axioms` `\<not> col A B C`] by blast
	have "seg_eq B C E D" using square_f[OF `axioms` `square B C E D`] by blast
	have "E \<noteq> D" using nullsegment3[OF `axioms` `B \<noteq> C` `seg_eq B C E D`] .
	have "D \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> D`] .
	have "oppo_side D C B A" using `oppo_side D C B A` .
	obtain q where "bet D q A \<and> col C B q \<and> \<not> col C B D" using oppositeside_f[OF `axioms` `oppo_side D C B A`]  by  blast
	have "bet D q A" using `bet D q A \<and> col C B q \<and> \<not> col C B D` by blast
	have "col C B q" using `bet D q A \<and> col C B q \<and> \<not> col C B D` by blast
	have "\<not> col C B D" using `bet D N A \<and> col C B N \<and> \<not> col C B D` by blast
	have "parallelogram B C E D" using squareparallelogram[OF `axioms` `square B C E D`] .
	have "parallel B C E D" using parallelogram_f[OF `axioms` `parallelogram B C E D`] by blast
	have "\<not> (meets B C E D)" using parallel_f[OF `axioms` `parallel B C E D`] by fastforce
	have "\<not> (A = E)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> E)"
		hence "A = E" by blast
		have "bet D q E" using `bet D q A` `A = E` by blast
		have "col D q E" using collinear_b `axioms` `bet D q E` by blast
		have "col E D q" using collinearorder[OF `axioms` `col D q E`] by blast
		have "col B C q" using collinearorder[OF `axioms` `col C B q`] by blast
		have "meets B C E D" using meet_b[OF `axioms` `B \<noteq> C` `E \<noteq> D` `col B C q` `col E D q`] .
		show "False" using `meets B C E D` `\<not> (meets B C E D)` by blast
	qed
	hence "A \<noteq> E" by blast
	have "\<not> (col D E A)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col D E A))"
hence "col D E A" by blast
		have "col D A E" using collinearorder[OF `axioms` `col D E A`] by blast
		have "col D q A" using collinear_b `axioms` `bet D q A \<and> col C B q \<and> \<not> col C B D` by blast
		have "col D A q" using collinearorder[OF `axioms` `col D q A`] by blast
		have "D \<noteq> A" using betweennotequal[OF `axioms` `bet D N A`] by blast
		have "col A E q" using collinear4[OF `axioms` `col D A E` `col D A q` `D \<noteq> A`] .
		have "col q A E" using collinearorder[OF `axioms` `col A E q`] by blast
		have "col q A D" using collinearorder[OF `axioms` `col D A q`] by blast
		have "q \<noteq> A" using betweennotequal[OF `axioms` `bet D q A`] by blast
		have "col A E D" using collinear4[OF `axioms` `col q A E` `col q A D` `q \<noteq> A`] .
		have "col A E q" using collinearorder[OF `axioms` `col q A E`] by blast
		have "col E D q" using collinear4[OF `axioms` `col A E D` `col A E q` `A \<noteq> E`] .
		have "col B C q" using collinearorder[OF `axioms` `col C B q`] by blast
		have "meets B C E D" using meet_b[OF `axioms` `B \<noteq> C` `E \<noteq> D` `col B C q` `col E D q`] .
		show "False" using `meets B C E D` `\<not> (meets B C E D)` by blast
	qed
	hence "\<not> col D E A" by blast
	obtain L where "perp_at A L D E L" using Prop12[OF `axioms` `D \<noteq> E` `\<not> col D E A`]  by  blast
	obtain p where "col A L L \<and> col D E L \<and> col D E p \<and> ang_right p L A" using perpat_f[OF `axioms` `perp_at A L D E L`]  by  blast
	have "col D E L" using `col A L L \<and> col D E L \<and> col D E p \<and> ang_right p L A` by blast
	have "col D E p" using `col A L L \<and> col D E L \<and> col D E p \<and> ang_right p L A` by blast
	have "ang_right p L A" using `col A L L \<and> col D E L \<and> col D E p \<and> ang_right p L A` by blast
	have "ang_right A L p" using n8_2[OF `axioms` `ang_right p L A`] .
	have "\<not> (B = N)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> N)"
		hence "B = N" by blast
		have "bet D B A" using `bet D N A` `B = N` by blast
		have "col D B A" using collinear_b `axioms` `bet D B A` by blast
		have "ang_right D B C" using square_f[OF `axioms` `square B C E D`] by blast
		have "ang_right A B C" using collinearright[OF `axioms` `ang_right D B C` `col D B A` `A \<noteq> B`] .
		have "\<not> (ang_right C A B)" using n8_7[OF `axioms` `ang_right A B C`] .
		have "ang_right C A B" using n8_2[OF `axioms` `ang_right B A C`] .
		show "False" using `ang_right C A B` `\<not> (ang_right C A B)` by blast
	qed
	hence "B \<noteq> N" by blast
	have "parallelogram B C E D" using `parallelogram B C E D` .
	have "parallel B C E D" using parallelogram_f[OF `axioms` `parallelogram B C E D`] by blast
	have "parallel B C D E" using parallelflip[OF `axioms` `parallel B C E D`] by blast
	have "parallel D E B C" using parallelsymmetric[OF `axioms` `parallel B C D E`] .
	have "parallel D E C B" using parallelflip[OF `axioms` `parallel D E B C`] by blast
	have "N \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> N`] .
	have "parallel D E N B" using collinearparallel[OF `axioms` `parallel D E C B` `col C B N` `N \<noteq> B`] .
	have "parallel D E B N" using parallelflip[OF `axioms` `parallel D E N B`] by blast
	have "tarski_parallel D E B N" using paralleldef2B[OF `axioms` `parallel D E B N`] .
	have "same_side B N D E" using tarski_parallel_f[OF `axioms` `tarski_parallel D E B N`] by blast
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "col D D E" using collinear_b `axioms` `D = D` by blast
	have "D \<noteq> N" using betweennotequal[OF `axioms` `bet D N A`] by blast
	have "ray_on D N A" using ray4 `axioms` `bet D N A \<and> col C B N \<and> \<not> col C B D` `D \<noteq> N` by blast
	have "same_side B A D E" using sameside2[OF `axioms` `same_side B N D E` `col D D E` `ray_on D N A`] .
	have "same_side B A E D" using samesideflip[OF `axioms` `same_side B A D E`] .
	have "same_side A B E D" using samesidesymmetric[OF `axioms` `same_side B A D E`] by blast
	have "\<not> (D = L)"
	proof (rule ccontr)
		assume "\<not> (D \<noteq> L)"
		hence "D = L" by blast
		have "ang_right A D p" using `ang_right A L p` `D = L` by blast
		have "ang_right p D A" using n8_2[OF `axioms` `ang_right A D p`] .
		have "col p D E" using collinearorder[OF `axioms` `col D E p`] by blast
		have "ang_right E D A" using collinearright[OF `axioms` `ang_right p D A` `col p D E` `E \<noteq> D`] .
		have "ang_right E D B" using square_f[OF `axioms` `square B C E D`] by blast
		have "same_side A B E D" using `same_side A B E D` .
		have "ray_on D A B" using erectedperpendicularunique[OF `axioms` `ang_right E D A` `ang_right E D B` `same_side A B E D`] .
		have "col D A B" using rayimpliescollinear[OF `axioms` `ray_on D A B`] .
		have "col A D B" using collinearorder[OF `axioms` `col D A B`] by blast
		have "col D N A" using collinear_b `axioms` `bet D N A \<and> col C B N \<and> \<not> col C B D` by blast
		have "col A D N" using collinearorder[OF `axioms` `col D N A`] by blast
		have "D \<noteq> A" using betweennotequal[OF `axioms` `bet D N A`] by blast
		have "A \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> A`] .
		have "col D B N" using collinear4[OF `axioms` `col A D B` `col A D N` `A \<noteq> D`] .
		have "col N B C" using collinearorder[OF `axioms` `col C B N`] by blast
		have "col N B D" using collinearorder[OF `axioms` `col D B N`] by blast
		have "col B C D" using collinear4[OF `axioms` `col N B C` `col N B D` `N \<noteq> B`] .
		have "\<not> col B C D" using NCorder[OF `axioms` `\<not> col C B D`] by blast
		show "False" using `\<not> col B C D` `col B C D` by blast
	qed
	hence "D \<noteq> L" by blast
	have "L \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> L`] .
	have "parallel B C E D" using parallelflip[OF `axioms` `parallel B C D E`] by blast
	have "col E D L" using collinearorder[OF `axioms` `col D E L`] by blast
	have "parallel B C L D" using collinearparallel[OF `axioms` `parallel B C E D` `col E D L` `L \<noteq> D`] .
	have "parallel L D B C" using parallelsymmetric[OF `axioms` `parallel B C L D`] .
	have "tarski_parallel B C L D" using paralleldef2B[OF `axioms` `parallel B C L D`] .
	have "same_side L D B C" using tarski_parallel_f[OF `axioms` `tarski_parallel B C L D`] by blast
	have "\<not> col B C D" using parallelNC[OF `axioms` `parallel B C D E`] by blast
	have "col B C N" using collinearorder[OF `axioms` `col C B N`] by blast
	have "oppo_side D B C A" using oppositeside_b[OF `axioms` `bet D N A` `col B C N` `\<not> col B C D`] .
	have "oppo_side L B C A" using planeseparation[OF `axioms` `same_side L D B C` `oppo_side D B C A`] .
	obtain M where "bet L M A \<and> col B C M \<and> \<not> col B C L" using oppositeside_f[OF `axioms` `oppo_side L B C A`]  by  blast
	have "bet L M A" using `bet L M A \<and> col B C M \<and> \<not> col B C L` by blast
	have "col B C M" using `bet L M A \<and> col B C M \<and> \<not> col B C L` by blast
	have "D \<noteq> E" using NCdistinct[OF `axioms` `\<not> col D E A`] by blast
	have "E \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> E`] .
	have "L \<noteq> M" using betweennotequal[OF `axioms` `bet L M A`] by blast
	have "ray_on L M A" using ray4 `axioms` `bet L M A \<and> col B C M \<and> \<not> col B C L` `L \<noteq> M` by blast
	have "ray_on L A M" using ray5[OF `axioms` `ray_on L M A`] .
	have "ang_right E D B" using square_f[OF `axioms` `square B C E D`] by blast
	have "ang_right p L A" using `ang_right p L A` .
	have "col D E p" using `col D E p` .
	have "col E D p" using collinearorder[OF `axioms` `col D E p`] by blast
	have "col E D L" using collinearorder[OF `axioms` `col D E L`] by blast
	have "col D p L" using collinear4[OF `axioms` `col E D p` `col E D L` `E \<noteq> D`] .
	have "col p L D" using collinearorder[OF `axioms` `col D p L`] by blast
	have "ang_right D L A" using collinearright[OF `axioms` `ang_right p L A` `col p L D` `D \<noteq> L`] .
	have "ang_right D L M" using n8_3[OF `axioms` `ang_right D L A` `ray_on L A M`] .
	have "\<not> (B = M)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> M)"
		hence "B = M" by blast
		have "ang_right D L B" using `ang_right D L M` `B = M` by blast
		have "ang_right L D B" using collinearright[OF `axioms` `ang_right E D B` `col E D L` `L \<noteq> D`] .
		have "ang_right B D L" using n8_2[OF `axioms` `ang_right L D B`] .
		have "\<not> (ang_right B D L)" using n8_7[OF `axioms` `ang_right D L B`] .
		show "False" using `\<not> (ang_right B D L)` `ang_right B D L` by blast
	qed
	hence "B \<noteq> M" by blast
	have "M \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> M`] .
	have "parallel L D C B" using parallelflip[OF `axioms` `parallel L D B C`] by blast
	have "col C B M" using collinearorder[OF `axioms` `col B C M`] by blast
	have "parallel L D M B" using collinearparallel[OF `axioms` `parallel L D C B` `col C B M` `M \<noteq> B`] .
	have "parallel L D B M" using parallelflip[OF `axioms` `parallel L D M B`] by blast
	have "parallel B M L D" using parallelsymmetric[OF `axioms` `parallel L D B M`] .
	have "parallel B M D L" using parallelflip[OF `axioms` `parallel B M L D`] by blast
	have "parallel D L B M" using parallelsymmetric[OF `axioms` `parallel B M D L`] .
	have "tarski_parallel D L B M" using paralleldef2B[OF `axioms` `parallel D L B M`] .
	have "same_side B M D L" using tarski_parallel_f[OF `axioms` `tarski_parallel D L B M`] by blast
	have "parallel B M L D" using parallelsymmetric[OF `axioms` `parallel L D B M`] .
	have "ang_right L D B" using collinearright[OF `axioms` `ang_right E D B` `col E D L` `L \<noteq> D`] .
	have "ang_right B D L" using n8_2[OF `axioms` `ang_right L D B`] .
	have "parallel B D L M" using twoperpsparallel[OF `axioms` `ang_right B D L` `ang_right D L M` `same_side B M D L`] .
	have "parallel B D M L" using parallelflip[OF `axioms` `parallel B D L M`] by blast
	have "parallelogram B M L D" using parallelogram_b[OF `axioms` `parallel B M L D` `parallel B D M L`] .
	have "parallel M L B D" using parallelsymmetric[OF `axioms` `parallel B D M L`] .
	have "tarski_parallel M L B D" using paralleldef2B[OF `axioms` `parallel M L B D`] .
	have "same_side B D M L" using tarski_parallel_f[OF `axioms` `tarski_parallel M L B D`] by blast
	have "bet A M L" using betweennesssymmetryE[OF `axioms` `bet L M A`] .
	have "parallel M B L D" using parallelflip[OF `axioms` `parallel B M D L`] by blast
	have "ang_eq A M B M L D" using Prop29C[OF `axioms` `parallel M B L D` `same_side B D M L` `bet A M L`] by blast
	have "ang_right M L D" using n8_2[OF `axioms` `ang_right D L M`] .
	have "ang_right A M B" using equaltorightisright[OF `axioms` `ang_right M L D` `ang_eq A M B M L D`] .
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "col B C B" using collinear_b `axioms` `B = B` by blast
	have "bet B M C" using altitudeofrighttriangle[OF `axioms` `ang_right B A C` `ang_right A M B` `col B C B` `col B C M`] .
	have "\<not> (M = C)"
	proof (rule ccontr)
		assume "\<not> (M \<noteq> C)"
		hence "M = C" by blast
		have "ang_right A M B" using `ang_right A M B` .
		have "ang_right A C B" using `ang_right A M B` `M = C` by blast
		have "\<not> (ang_right B A C)" using n8_7[OF `axioms` `ang_right A C B`] .
		show "False" using `\<not> (ang_right B A C)` `ang_right B A C` by blast
	qed
	hence "M \<noteq> C" by blast
	have "\<not> (L = E)"
	proof (rule ccontr)
		assume "\<not> (L \<noteq> E)"
		hence "L = E" by blast
		have "parallelogram B C E D" using `parallelogram B C E D` .
		have "parallel B D C E" using parallelogram_f[OF `axioms` `parallelogram B C E D`] by blast
		have "parallel C E B D" using parallelsymmetric[OF `axioms` `parallel B D C E`] .
		have "parallel M E B D" using `parallel M L B D` `L = E` by blast
		have "parallel B D M E" using parallelsymmetric[OF `axioms` `parallel M E B D`] .
		have "parallel B D C E" using parallelsymmetric[OF `axioms` `parallel C E B D`] .
		have "parallel B D E C" using parallelflip[OF `axioms` `parallel B D C E`] by blast
		have "parallel B D E M" using parallelflip[OF `axioms` `parallel B D M E`] by blast
		have "col E C M" using Playfair[OF `axioms` `parallel B D E C` `parallel B D E M`] .
		have "col M C E" using collinearorder[OF `axioms` `col E C M`] by blast
		have "col M C B" using collinearorder[OF `axioms` `col B C M`] by blast
		have "M \<noteq> C" using `M \<noteq> C` .
		have "col C E B" using collinear4[OF `axioms` `col M C E` `col M C B` `M \<noteq> C`] .
		have "col B C E" using collinearorder[OF `axioms` `col C E B`] by blast
		have "\<not> col B C E" using parallelNC[OF `axioms` `parallel B C D E`] by blast
		show "False" using `\<not> col B C E` `col B C E` by blast
	qed
	hence "L \<noteq> E" by blast
	have "parallel B M L D" using parallelogram_f[OF `axioms` `parallelogram B M L D`] by blast
	have "parallel B M D L" using parallelflip[OF `axioms` `parallel B M L D`] by blast
	have "col D L E" using collinearorder[OF `axioms` `col D E L`] by blast
	have "E \<noteq> L" using inequalitysymmetric[OF `axioms` `L \<noteq> E`] .
	have "parallel B M E L" using collinearparallel[OF `axioms` `parallel B M D L` `col D L E` `E \<noteq> L`] .
	have "parallel E L B M" using parallelsymmetric[OF `axioms` `parallel B M E L`] .
	have "col B M C" using collinearorder[OF `axioms` `col B C M`] by blast
	have "C \<noteq> M" using inequalitysymmetric[OF `axioms` `M \<noteq> C`] .
	have "parallel E L C M" using collinearparallel[OF `axioms` `parallel E L B M` `col B M C` `C \<noteq> M`] .
	have "parallel C M E L" using parallelsymmetric[OF `axioms` `parallel E L C M`] .
	have "parallel M C E L" using parallelflip[OF `axioms` `parallel C M E L`] by blast
	have "ang_right D L M" using `ang_right D L M` .
	have "col D L E" using collinearorder[OF `axioms` `col D E L`] by blast
	have "ang_right E L M" using collinearright[OF `axioms` `ang_right D L M` `col D L E` `E \<noteq> L`] .
	have "ang_right M L E" using n8_2[OF `axioms` `ang_right E L M`] .
	have "ang_right C E D" using square_f[OF `axioms` `square B C E D`] by blast
	have "ang_right D E C" using n8_2[OF `axioms` `ang_right C E D`] .
	have "col D E L" using `col D E L` .
	have "L \<noteq> E" using `L \<noteq> E` .
	have "ang_right L E C" using collinearright[OF `axioms` `ang_right D E C` `col D E L` `L \<noteq> E`] .
	have "parallel M C L E" using parallelflip[OF `axioms` `parallel C M E L`] by blast
	have "parallel L E M C" using parallelsymmetric[OF `axioms` `parallel M C L E`] .
	have "tarski_parallel L E M C" using paralleldef2B[OF `axioms` `parallel L E M C`] .
	have "same_side M C L E" using tarski_parallel_f[OF `axioms` `tarski_parallel L E M C`] by blast
	have "parallel M L E C" using twoperpsparallel[OF `axioms` `ang_right M L E` `ang_right L E C` `same_side M C L E`] .
	have "parallel M L C E" using parallelflip[OF `axioms` `parallel M L E C`] by blast
	have "parallelogram M C E L" using parallelogram_b[OF `axioms` `parallel M C E L` `parallel M L C E`] .
	have "seg_eq B M D L" using Prop34[OF `axioms` `parallelogram B M L D`] by blast
	have "seg_eq M C L E" using Prop34[OF `axioms` `parallelogram M C E L`] by blast
	have "seg_eq B C D E" using Prop34[OF `axioms` `parallelogram B C E D`] by blast
	have "bet B M C" using `bet B M C` .
	have "bet D L E" using betweennesspreserved[OF `axioms` `seg_eq B M D L` `seg_eq B C D E` `seg_eq M C L E` `bet B M C`] .
	have "parallelogram B M L D \<and> bet B M C \<and> parallelogram M C E L \<and> bet D L E \<and> bet L M A \<and> ang_right D L A" using `parallelogram B M L D` `bet B M C` `parallelogram M C E L` `bet D L E` `bet L M A \<and> col B C M \<and> \<not> col B C L` `ang_right D L A` by blast
	thus ?thesis by blast
qed

end