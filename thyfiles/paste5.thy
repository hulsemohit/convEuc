theory paste5
	imports Geometry Prop34 betweennotequal collinear4 collinearorder collinearparallel crisscross crossimpliesopposite diagonalsmeet inequalitysymmetric oppositesidesymmetric parallelNC paralleldef2B parallelflip parallelsymmetric ray4 rectangleparallelogram samenotopposite sameside2 samesidesymmetric
begin

theorem(in euclidean_geometry) paste5:
	assumes 
		"qua_eq_area B M L D b m l d"
		"qua_eq_area M C E L m c e l"
		"bet B M C"
		"bet b m c"
		"bet E L D"
		"bet e l d"
		"rectangle M C E L"
		"rectangle m c e l"
	shows "qua_eq_area B C E D b c e d"
proof -
	have "parallelogram M C E L" using rectangleparallelogram[OF `rectangle M C E L`] .
	have "parallelogram m c e l" using rectangleparallelogram[OF `rectangle m c e l`] .
	obtain P where "bet M P E \<and> bet C P L" using diagonalsmeet[OF `parallelogram M C E L`]  by  blast
	obtain p where "bet m p e \<and> bet c p l" using diagonalsmeet[OF `parallelogram m c e l`]  by  blast
	have "bet M P E" using `bet M P E \<and> bet C P L` by blast
	have "bet C P L" using `bet M P E \<and> bet C P L` by blast
	have "bet m p e" using `bet m p e \<and> bet c p l` by blast
	have "bet c p l" using `bet m p e \<and> bet c p l` by blast
	have "parallel M C E L" using parallelogram_f[OF `parallelogram M C E L`] by blast
	have "\<not> col M C L" using parallelNC[OF `parallel M C E L`] by blast
	have "parallel m c e l" using parallelogram_f[OF `parallelogram m c e l`] by blast
	have "\<not> col m c l" using parallelNC[OF `parallel m c e l`] by blast
	have "tri_cong C M L L E C" using Prop34[OF `parallelogram M C E L`] by blast
	have "tri_cong c m l l e c" using Prop34[OF `parallelogram m c e l`] by blast
	have "tri_eq_area C M L L E C" using congruentequalE[OF `tri_cong C M L L E C`] .
	have "tri_eq_area c m l l e c" using congruentequalE[OF `tri_cong c m l l e c`] .
	have "cross M E C L" using rectangle_f[OF `rectangle M C E L`] by blast
	have "cross m e c l" using rectangle_f[OF `rectangle m c e l`] by blast
	have "tri_eq_area c m l c l e" using ETpermutationE[OF `tri_eq_area c m l l e c`] by blast
	have "tri_eq_area c l e c m l" using ETsymmetricE[OF `tri_eq_area c m l c l e`] .
	have "tri_eq_area c l e m c l" using ETpermutationE[OF `tri_eq_area c l e c m l`] by blast
	have "tri_eq_area m c l c l e" using ETsymmetricE[OF `tri_eq_area c l e m c l`] .
	have "tri_eq_area C M L C L E" using ETpermutationE[OF `tri_eq_area C M L L E C`] by blast
	have "tri_eq_area C L E C M L" using ETsymmetricE[OF `tri_eq_area C M L C L E`] .
	have "tri_eq_area C L E M C L" using ETpermutationE[OF `tri_eq_area C L E C M L`] by blast
	have "tri_eq_area M C L C L E" using ETsymmetricE[OF `tri_eq_area C L E M C L`] .
	have "oppo_side M C L E" using crossimpliesopposite[OF `cross M E C L` `\<not> col M C L`] by blast
	have "oppo_side m c l e" using crossimpliesopposite[OF `cross m e c l` `\<not> col m c l`] by blast
	have "tri_eq_area M C L m c l" using halvesofequalsE[OF `tri_eq_area M C L C L E` `oppo_side M C L E` `tri_eq_area m c l c l e` `oppo_side m c l e` `qua_eq_area M C E L m c e l`] .
	have "qua_eq_area M C E L e c m l" using EFpermutationE[OF `qua_eq_area M C E L m c e l`] by blast
	have "qua_eq_area e c m l M C E L" using EFsymmetricE[OF `qua_eq_area M C E L e c m l`] .
	have "qua_eq_area e c m l E C M L" using EFpermutationE[OF `qua_eq_area e c m l M C E L`] by blast
	have "qua_eq_area E C M L e c m l" using EFsymmetricE[OF `qua_eq_area e c m l E C M L`] .
	have "oppo_side E C L M" using oppositesidesymmetric[OF `oppo_side M C L E`] .
	have "oppo_side e c l m" using oppositesidesymmetric[OF `oppo_side m c l e`] .
	have "tri_eq_area M C L E C L" using ETpermutationE[OF `tri_eq_area M C L C L E`] by blast
	have "tri_eq_area E C L M C L" using ETsymmetricE[OF `tri_eq_area M C L E C L`] .
	have "tri_eq_area E C L C L M" using ETpermutationE[OF `tri_eq_area E C L M C L`] by blast
	have "tri_eq_area m c l e c l" using ETpermutationE[OF `tri_eq_area m c l c l e`] by blast
	have "tri_eq_area e c l m c l" using ETsymmetricE[OF `tri_eq_area m c l e c l`] .
	have "tri_eq_area e c l c l m" using ETpermutationE[OF `tri_eq_area e c l m c l`] by blast
	have "tri_eq_area E C L e c l" using halvesofequalsE[OF `tri_eq_area E C L C L M` `oppo_side E C L M` `tri_eq_area e c l c l m` `oppo_side e c l m` `qua_eq_area E C M L e c m l`] .
	have "qua_eq_area B M L D d b m l" using EFpermutationE[OF `qua_eq_area B M L D b m l d`] by blast
	have "qua_eq_area d b m l B M L D" using EFsymmetricE[OF `qua_eq_area B M L D d b m l`] .
	have "qua_eq_area d b m l D B M L" using EFpermutationE[OF `qua_eq_area d b m l B M L D`] by blast
	have "qua_eq_area D B M L d b m l" using EFsymmetricE[OF `qua_eq_area d b m l D B M L`] .
	have "col B M C" using collinear_b `bet B M C` by blast
	have "col M C B" using collinearorder[OF `col B M C`] by blast
	have "B \<noteq> C" using betweennotequal[OF `bet B M C`] by blast
	have "parallel E L M C" using parallelsymmetric[OF `parallel M C E L`] .
	have "parallel E L B C" using collinearparallel[OF `parallel E L M C` `col M C B` `B \<noteq> C`] .
	have "parallel B C E L" using parallelsymmetric[OF `parallel E L B C`] .
	have "col E L D" using collinear_b `bet E L D` by blast
	have "L \<noteq> D" using betweennotequal[OF `bet E L D`] by blast
	have "D \<noteq> L" using inequalitysymmetric[OF `L \<noteq> D`] .
	have "parallel B C D L" using collinearparallel[OF `parallel B C E L` `col E L D` `D \<noteq> L`] .
	have "E \<noteq> L" using betweennotequal[OF `bet E L D`] by blast
	have "M \<noteq> C" using betweennotequal[OF `bet B M C`] by blast
	have "\<not> (cross B D C L)"
	proof (rule ccontr)
		assume "\<not> (\<not> (cross B D C L))"
hence "cross B D C L" by blast
		have "\<not> (col C L M)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col C L M))"
hence "col C L M" by blast
			have "col M C L" using collinearorder[OF `col C L M`] by blast
			have "L = L" using equalityreflexiveE.
			have "col E L L" using collinear_b `L = L` by blast
			have "meets E L M C" using meet_b[OF `E \<noteq> L` `M \<noteq> C` `col E L L` `col M C L`] .
			have "\<not> (meets E L M C)" using parallel_f[OF `parallel E L M C`] by fastforce
			show "False" using `\<not> (meets E L M C)` `meets E L M C` by blast
		qed
		hence "\<not> col C L M" by blast
		have "\<not> (col C L D)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col C L D))"
hence "col C L D" by blast
			have "col D L C" using collinearorder[OF `col C L D`] by blast
			have "col E L D" using collinear_b `bet E L D` by blast
			have "col D L E" using collinearorder[OF `col E L D`] by blast
			have "L \<noteq> D" using betweennotequal[OF `bet E L D`] by blast
			have "D \<noteq> L" using inequalitysymmetric[OF `L \<noteq> D`] .
			have "col L E C" using collinear4[OF `col D L E` `col D L C` `D \<noteq> L`] .
			have "col E L C" using collinearorder[OF `col L E C`] by blast
			have "C = C" using equalityreflexiveE.
			have "col M C C" using collinear_b `C = C` by blast
			have "meets E L M C" using meet_b[OF `E \<noteq> L` `M \<noteq> C` `col E L C` `col M C C`] .
			have "\<not> (meets E L M C)" using parallel_f[OF `parallel E L M C`] by fastforce
			show "False" using `\<not> (meets E L M C)` `meets E L M C` by blast
		qed
		hence "\<not> col C L D" by blast
		have "L = L" using equalityreflexiveE.
		have "col C L L" using collinear_b `L = L` by blast
		have "bet D L E" using betweennesssymmetryE[OF `bet E L D`] .
		have "bet M P E" using `bet M P E` .
		have "col C L P" using collinear_b `bet M P E \<and> bet C P L` by blast
		have "same_side D M C L" using sameside_b[OF `col C L L` `col C L P` `bet D L E` `bet M P E` `\<not> col C L D` `\<not> col C L M`] .
		have "bet C M B" using betweennesssymmetryE[OF `bet B M C`] .
		have "C \<noteq> M" using betweennotequal[OF `bet C M B`] by blast
		have "ray_on C M B" using ray4 `bet C M B` `C \<noteq> M` by blast
		have "C = C" using equalityreflexiveE.
		have "col C C L" using collinear_b `C = C` by blast
		have "same_side D B C L" using sameside2[OF `same_side D M C L` `col C C L` `ray_on C M B`] .
		have "same_side B D C L" using samesidesymmetric[OF `same_side D B C L`] by blast
		have "\<not> (oppo_side B C L D)" using samenotopposite[OF `same_side B D C L`] .
		have "\<not> (col B C L)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col B C L))"
hence "col B C L" by blast
			have "col B M C" using collinear_b `bet B M C` by blast
			have "col B C M" using collinearorder[OF `col B M C`] by blast
			have "B \<noteq> C" using betweennotequal[OF `bet B M C`] by blast
			have "col C M L" using collinear4[OF `col B C M` `col B C L` `B \<noteq> C`] .
			have "col M C L" using collinearorder[OF `col C M L`] by blast
			have "col E L L" using collinear_b `L = L` by blast
			have "meets E L M C" using meet_b[OF `E \<noteq> L` `M \<noteq> C` `col E L L` `col M C L`] .
			have "\<not> (meets E L M C)" using parallel_f[OF `parallel E L M C`] by fastforce
			show "False" using `\<not> (meets E L M C)` `meets E L M C` by blast
		qed
		hence "\<not> col B C L" by blast
		have "oppo_side B C L D" using crossimpliesopposite[OF `cross B D C L` `\<not> col B C L`] by blast
		show "False" using `oppo_side B C L D` `\<not> (oppo_side B C L D)` by blast
	qed
	hence "\<not> (cross B D C L)" by blast
	have "parallel B C D L" using `parallel B C D L` .
	have "cross B L D C" using crisscross[OF `parallel B C D L` `\<not> (cross B D C L)`] .
	obtain R where "bet B R L \<and> bet D R C" using cross_f[OF `cross B L D C`]  by  blast
	have "bet D R C" using `bet B R L \<and> bet D R C` by blast
	have "bet B R L" using `bet B R L \<and> bet D R C` by blast
	have "col b m c" using collinear_b `bet b m c` by blast
	have "col m c b" using collinearorder[OF `col b m c`] by blast
	have "b \<noteq> c" using betweennotequal[OF `bet b m c`] by blast
	have "parallel e l m c" using parallelsymmetric[OF `parallel m c e l`] .
	have "parallel e l b c" using collinearparallel[OF `parallel e l m c` `col m c b` `b \<noteq> c`] .
	have "parallel b c e l" using parallelsymmetric[OF `parallel e l b c`] .
	have "col e l d" using collinear_b `bet e l d` by blast
	have "l \<noteq> d" using betweennotequal[OF `bet e l d`] by blast
	have "d \<noteq> l" using inequalitysymmetric[OF `l \<noteq> d`] .
	have "parallel b c d l" using collinearparallel[OF `parallel b c e l` `col e l d` `d \<noteq> l`] .
	have "e \<noteq> l" using betweennotequal[OF `bet e l d`] by blast
	have "m \<noteq> c" using betweennotequal[OF `bet b m c`] by blast
	have "\<not> (cross b d c l)"
	proof (rule ccontr)
		assume "\<not> (\<not> (cross b d c l))"
hence "cross b d c l" by blast
		have "\<not> (col c l m)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col c l m))"
hence "col c l m" by blast
			have "col m c l" using collinearorder[OF `col c l m`] by blast
			have "l = l" using equalityreflexiveE.
			have "col e l l" using collinear_b `l = l` by blast
			have "meets e l m c" using meet_b[OF `e \<noteq> l` `m \<noteq> c` `col e l l` `col m c l`] .
			have "\<not> (meets e l m c)" using parallel_f[OF `parallel e l m c`] by fastforce
			show "False" using `\<not> (meets e l m c)` `meets e l m c` by blast
		qed
		hence "\<not> col c l m" by blast
		have "\<not> (col c l d)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col c l d))"
hence "col c l d" by blast
			have "col d l c" using collinearorder[OF `col c l d`] by blast
			have "col e l d" using collinear_b `bet e l d` by blast
			have "col d l e" using collinearorder[OF `col e l d`] by blast
			have "l \<noteq> d" using betweennotequal[OF `bet e l d`] by blast
			have "d \<noteq> l" using inequalitysymmetric[OF `l \<noteq> d`] .
			have "col l e c" using collinear4[OF `col d l e` `col d l c` `d \<noteq> l`] .
			have "col e l c" using collinearorder[OF `col l e c`] by blast
			have "c = c" using equalityreflexiveE.
			have "col m c c" using collinear_b `c = c` by blast
			have "meets e l m c" using meet_b[OF `e \<noteq> l` `m \<noteq> c` `col e l c` `col m c c`] .
			have "\<not> (meets e l m c)" using parallel_f[OF `parallel e l m c`] by fastforce
			show "False" using `\<not> (meets e l m c)` `meets e l m c` by blast
		qed
		hence "\<not> col c l d" by blast
		have "l = l" using equalityreflexiveE.
		have "col c l l" using collinear_b `l = l` by blast
		have "bet d l e" using betweennesssymmetryE[OF `bet e l d`] .
		have "bet m p e" using `bet m p e` .
		have "col c l p" using collinear_b `bet m p e \<and> bet c p l` by blast
		have "same_side d m c l" using sameside_b[OF `col c l l` `col c l p` `bet d l e` `bet m p e` `\<not> col c l d` `\<not> col c l m`] .
		have "bet c m b" using betweennesssymmetryE[OF `bet b m c`] .
		have "c \<noteq> m" using betweennotequal[OF `bet c m b`] by blast
		have "ray_on c m b" using ray4 `bet c m b` `c \<noteq> m` by blast
		have "c = c" using equalityreflexiveE.
		have "col c c l" using collinear_b `c = c` by blast
		have "same_side d b c l" using sameside2[OF `same_side d m c l` `col c c l` `ray_on c m b`] .
		have "same_side b d c l" using samesidesymmetric[OF `same_side d b c l`] by blast
		have "\<not> (oppo_side b c l d)" using samenotopposite[OF `same_side b d c l`] .
		have "\<not> (col b c l)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col b c l))"
hence "col b c l" by blast
			have "col b m c" using collinear_b `bet b m c` by blast
			have "col b c m" using collinearorder[OF `col b m c`] by blast
			have "b \<noteq> c" using betweennotequal[OF `bet b m c`] by blast
			have "col c m l" using collinear4[OF `col b c m` `col b c l` `b \<noteq> c`] .
			have "col m c l" using collinearorder[OF `col c m l`] by blast
			have "col e l l" using collinear_b `l = l` by blast
			have "meets e l m c" using meet_b[OF `e \<noteq> l` `m \<noteq> c` `col e l l` `col m c l`] .
			have "\<not> (meets e l m c)" using parallel_f[OF `parallel e l m c`] by fastforce
			show "False" using `\<not> (meets e l m c)` `meets e l m c` by blast
		qed
		hence "\<not> col b c l" by blast
		have "oppo_side b c l d" using crossimpliesopposite[OF `cross b d c l` `\<not> col b c l`] by blast
		show "False" using `oppo_side b c l d` `\<not> (oppo_side b c l d)` by blast
	qed
	hence "\<not> (cross b d c l)" by blast
	have "parallel b c d l" using `parallel b c d l` .
	have "cross b l d c" using crisscross[OF `parallel b c d l` `\<not> (cross b d c l)`] .
	obtain r where "bet b r l \<and> bet d r c" using cross_f[OF `cross b l d c`]  by  blast
	have "bet d r c" using `bet b r l \<and> bet d r c` by blast
	have "bet b r l" using `bet b r l \<and> bet d r c` by blast
	have "qua_eq_area D B C L d b c l" using paste2E[OF `bet B M C` `bet b m c` `tri_eq_area M C L m c l` `qua_eq_area D B M L d b m l` `bet D R C` `bet B R L` `bet d r c` `bet b r l`] .
	have "qua_eq_area D B C L b d l c" using EFpermutationE[OF `qua_eq_area D B C L d b c l`] by blast
	have "qua_eq_area b d l c D B C L" using EFsymmetricE[OF `qua_eq_area D B C L b d l c`] .
	have "qua_eq_area b d l c B D L C" using EFpermutationE[OF `qua_eq_area b d l c D B C L`] by blast
	have "qua_eq_area B D L C b d l c" using EFsymmetricE[OF `qua_eq_area b d l c B D L C`] .
	have "tri_eq_area E C L l e c" using ETpermutationE[OF `tri_eq_area E C L e c l`] by blast
	have "tri_eq_area l e c E C L" using ETsymmetricE[OF `tri_eq_area E C L l e c`] .
	have "tri_eq_area l e c L E C" using ETpermutationE[OF `tri_eq_area l e c E C L`] by blast
	have "tri_eq_area L E C l e c" using ETsymmetricE[OF `tri_eq_area l e c L E C`] .
	have "bet D L E" using betweennesssymmetryE[OF `bet E L D`] .
	have "bet d l e" using betweennesssymmetryE[OF `bet e l d`] .
	have "parallel B C E L" using `parallel B C E L` .
	have "parallel B C L E" using parallelflip[OF `parallel B C E L`] by blast
	have "col E L D" using collinear_b `bet E L D` by blast
	have "col L E D" using collinearorder[OF `col E L D`] by blast
	have "E \<noteq> D" using betweennotequal[OF `bet E L D`] by blast
	have "D \<noteq> E" using inequalitysymmetric[OF `E \<noteq> D`] .
	have "parallel B C D E" using collinearparallel[OF `parallel B C L E` `col L E D` `D \<noteq> E`] .
	have "parallel M L C E" using parallelogram_f[OF `parallelogram M C E L`] by blast
	have "parallel C E M L" using parallelsymmetric[OF `parallel M L C E`] .
	have "tarski_parallel C E M L" using paralleldef2B[OF `parallel C E M L`] .
	have "same_side M L C E" using tarski_parallel_f[OF `tarski_parallel C E M L`] by blast
	have "same_side L M C E" using samesidesymmetric[OF `same_side M L C E`] by blast
	have "M \<noteq> C" using betweennotequal[OF `bet B M C`] by blast
	have "C \<noteq> M" using inequalitysymmetric[OF `M \<noteq> C`] .
	have "bet C M B" using betweennesssymmetryE[OF `bet B M C`] .
	have "ray_on C M B" using ray4 `bet C M B` `C \<noteq> M` by blast
	have "C = C" using equalityreflexiveE.
	have "col C C E" using collinear_b `C = C` by blast
	have "same_side L B C E" using sameside2[OF `same_side L M C E` `col C C E` `ray_on C M B`] .
	have "same_side B L C E" using samesidesymmetric[OF `same_side L B C E`] by blast
	have "E \<noteq> L" using betweennotequal[OF `bet E L D`] by blast
	have "ray_on E L D" using ray4 `bet E L D` `E \<noteq> L` by blast
	have "E = E" using equalityreflexiveE.
	have "col C E E" using collinear_b `E = E` by blast
	have "same_side B D C E" using sameside2[OF `same_side B L C E` `col C E E` `ray_on E L D`] .
	have "same_side D B C E" using samesidesymmetric[OF `same_side B D C E`] by blast
	have "\<not> (cross B D C E)"
	proof (rule ccontr)
		assume "\<not> (\<not> (cross B D C E))"
hence "cross B D C E" by blast
		have "\<not> (col B C E)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col B C E))"
hence "col B C E" by blast
			have "E = E" using equalityreflexiveE.
			have "col D E E" using collinear_b `E = E` by blast
			have "meets B C D E" using meet_b[OF `B \<noteq> C` `D \<noteq> E` `col B C E` `col D E E`] .
			have "\<not> (meets B C D E)" using parallel_f[OF `parallel B C D E`] by fastforce
			show "False" using `\<not> (meets B C D E)` `meets B C D E` by blast
		qed
		hence "\<not> col B C E" by blast
		have "oppo_side B C E D" using crossimpliesopposite[OF `cross B D C E` `\<not> col B C E`] by blast
		have "\<not> (oppo_side B C E D)" using samenotopposite[OF `same_side B D C E`] .
		show "False" using `\<not> (oppo_side B C E D)` `oppo_side B C E D` by blast
	qed
	hence "\<not> (cross B D C E)" by blast
	have "cross B E D C" using crisscross[OF `parallel B C D E` `\<not> (cross B D C E)`] .
	obtain T where "bet B T E \<and> bet D T C" using cross_f[OF `cross B E D C`]  by  blast
	have "bet B T E" using `bet B T E \<and> bet D T C` by blast
	have "bet D T C" using `bet B T E \<and> bet D T C` by blast
	have "parallel b c e l" using `parallel b c e l` .
	have "parallel b c l e" using parallelflip[OF `parallel b c e l`] by blast
	have "col e l d" using collinear_b `bet e l d` by blast
	have "col l e d" using collinearorder[OF `col e l d`] by blast
	have "e \<noteq> d" using betweennotequal[OF `bet e l d`] by blast
	have "d \<noteq> e" using inequalitysymmetric[OF `e \<noteq> d`] .
	have "parallel b c d e" using collinearparallel[OF `parallel b c l e` `col l e d` `d \<noteq> e`] .
	have "parallel m l c e" using parallelogram_f[OF `parallelogram m c e l`] by blast
	have "parallel c e m l" using parallelsymmetric[OF `parallel m l c e`] .
	have "tarski_parallel c e m l" using paralleldef2B[OF `parallel c e m l`] .
	have "same_side m l c e" using tarski_parallel_f[OF `tarski_parallel c e m l`] by blast
	have "same_side l m c e" using samesidesymmetric[OF `same_side m l c e`] by blast
	have "m \<noteq> c" using betweennotequal[OF `bet b m c`] by blast
	have "c \<noteq> m" using inequalitysymmetric[OF `m \<noteq> c`] .
	have "bet c m b" using betweennesssymmetryE[OF `bet b m c`] .
	have "ray_on c m b" using ray4 `bet c m b` `c \<noteq> m` by blast
	have "c = c" using equalityreflexiveE.
	have "col c c e" using collinear_b `c = c` by blast
	have "same_side l b c e" using sameside2[OF `same_side l m c e` `col c c e` `ray_on c m b`] .
	have "same_side b l c e" using samesidesymmetric[OF `same_side l b c e`] by blast
	have "e \<noteq> l" using betweennotequal[OF `bet e l d`] by blast
	have "ray_on e l d" using ray4 `bet e l d` `e \<noteq> l` by blast
	have "e = e" using equalityreflexiveE.
	have "col c e e" using collinear_b `e = e` by blast
	have "same_side b d c e" using sameside2[OF `same_side b l c e` `col c e e` `ray_on e l d`] .
	have "same_side d b c e" using samesidesymmetric[OF `same_side b d c e`] by blast
	have "\<not> (cross b d c e)"
	proof (rule ccontr)
		assume "\<not> (\<not> (cross b d c e))"
hence "cross b d c e" by blast
		have "\<not> (col b c e)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col b c e))"
hence "col b c e" by blast
			have "e = e" using equalityreflexiveE.
			have "col d e e" using collinear_b `e = e` by blast
			have "meets b c d e" using meet_b[OF `b \<noteq> c` `d \<noteq> e` `col b c e` `col d e e`] .
			have "\<not> (meets b c d e)" using parallel_f[OF `parallel b c d e`] by fastforce
			show "False" using `\<not> (meets b c d e)` `meets b c d e` by blast
		qed
		hence "\<not> col b c e" by blast
		have "oppo_side b c e d" using crossimpliesopposite[OF `cross b d c e` `\<not> col b c e`] by blast
		have "\<not> (oppo_side b c e d)" using samenotopposite[OF `same_side b d c e`] .
		show "False" using `\<not> (oppo_side b c e d)` `oppo_side b c e d` by blast
	qed
	hence "\<not> (cross b d c e)" by blast
	have "cross b e d c" using crisscross[OF `parallel b c d e` `\<not> (cross b d c e)`] .
	obtain t where "bet b t e \<and> bet d t c" using cross_f[OF `cross b e d c`]  by  blast
	have "bet b t e" using `bet b t e \<and> bet d t c` by blast
	have "bet d t c" using `bet b t e \<and> bet d t c` by blast
	have "qua_eq_area B D E C b d e c" using paste2E[OF `bet D L E` `bet d l e` `tri_eq_area L E C l e c` `qua_eq_area B D L C b d l c` `bet B T E` `bet D T C` `bet b t e` `bet d t c`] .
	have "qua_eq_area B D E C b c e d" using EFpermutationE[OF `qua_eq_area B D E C b d e c`] by blast
	have "qua_eq_area b c e d B D E C" using EFsymmetricE[OF `qua_eq_area B D E C b c e d`] .
	have "qua_eq_area b c e d B C E D" using EFpermutationE[OF `qua_eq_area b c e d B D E C`] by blast
	have "qua_eq_area B C E D b c e d" using EFsymmetricE[OF `qua_eq_area b c e d B C E D`] .
	thus ?thesis by blast
qed

end