theory Prop48
	imports n8_3 Geometry NCdistinct NChelper NCorder PGrectangle PGrotate Prop08 Prop11B Prop46 Prop47 Prop48A betweennotequal collinearorder collinearright congruencesymmetric equaltorightisright inequalitysymmetric layoff oppositesideflip paste5 rectanglerotate rightangleNC squaresequal
begin

theorem(in euclidean_geometry) Prop48:
	assumes 
		"triangle A B C"
		"square A B F G"
		"square A C K H"
		"square B C E D"
		"bet B M C"
		"bet E L D"
		"qua_eq_area A B F G B M L D"
		"qua_eq_area A C K H M C E L"
		"rectangle M C E L"
	shows "ang_right B A C"
proof -
	have "\<not> col A B C" using triangle_f[OF `triangle A B C`] .
	have "A \<noteq> C" using NCdistinct[OF `\<not> col A B C`] by blast
	have "A \<noteq> B" using NCdistinct[OF `\<not> col A B C`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	obtain R where "bet B A R \<and> seg_eq A R A B" using extensionE[OF `B \<noteq> A` `A \<noteq> B`]  by  blast
	have "bet B A R" using `bet B A R \<and> seg_eq A R A B` by blast
	have "col B A R" using collinear_b `bet B A R \<and> seg_eq A R A B` by blast
	have "col A B R" using collinearorder[OF `col B A R`] by blast
	have "B = B" using equalityreflexiveE.
	have "col A B B" using collinear_b `B = B` by blast
	have "B \<noteq> R" using betweennotequal[OF `bet B A R`] by blast
	have "R \<noteq> B" using inequalitysymmetric[OF `B \<noteq> R`] .
	have "\<not> col R B C" using NChelper[OF `\<not> col A B C` `col A B R` `col A B B` `R \<noteq> B`] .
	have "\<not> col B R C" using NCorder[OF `\<not> col R B C`] by blast
	obtain Q where "ang_right B A Q \<and> oppo_side Q B R C" using Prop11B[OF `bet B A R` `\<not> col B R C`]  by  blast
	have "ang_right B A Q" using `ang_right B A Q \<and> oppo_side Q B R C` by blast
	have "\<not> col B A Q" using rightangleNC[OF `ang_right B A Q`] .
	have "A \<noteq> Q" using NCdistinct[OF `\<not> col B A Q`] by blast
	obtain c where "ray_on A Q c \<and> seg_eq A c A C" using layoff[OF `A \<noteq> Q` `A \<noteq> C`]  by  blast
	have "ray_on A Q c" using `ray_on A Q c \<and> seg_eq A c A C` by blast
	have "seg_eq A c A C" using `ray_on A Q c \<and> seg_eq A c A C` by blast
	have "ang_right B A c" using n8_3[OF `ang_right B A Q` `ray_on A Q c`] .
	have "\<not> col B A c" using rightangleNC[OF `ang_right B A c`] .
	have "\<not> col A B c" using NCorder[OF `\<not> col B A c`] by blast
	obtain f g where "square A B f g \<and> oppo_side g A B c \<and> parallelogram A B f g" using Prop46[OF `A \<noteq> B` `\<not> col A B c`]  by  blast
	have "square A B f g" using `square A B f g \<and> oppo_side g A B c \<and> parallelogram A B f g` by blast
	have "oppo_side g A B c" using `square A B f g \<and> oppo_side g A B c \<and> parallelogram A B f g` by blast
	have "A \<noteq> c" using NCdistinct[OF `\<not> col A B c`] by blast
	have "\<not> col A c B" using NCorder[OF `\<not> col A B c`] by blast
	obtain h k where "square A c k h \<and> oppo_side h A c B \<and> parallelogram A c k h" using Prop46[OF `A \<noteq> c` `\<not> col A c B`]  by  blast
	have "square A c k h" using `square A c k h \<and> oppo_side h A c B \<and> parallelogram A c k h` by blast
	have "oppo_side h A c B" using `square A c k h \<and> oppo_side h A c B \<and> parallelogram A c k h` by blast
	have "B \<noteq> c" using NCdistinct[OF `\<not> col A B c`] by blast
	have "\<not> col B c A" using NCorder[OF `\<not> col A B c`] by blast
	obtain d e where "square B c e d \<and> oppo_side d B c A \<and> parallelogram B c e d" using Prop46[OF `B \<noteq> c` `\<not> col B c A`]  by  blast
	have "square B c e d" using `square B c e d \<and> oppo_side d B c A \<and> parallelogram B c e d` by blast
	have "oppo_side d B c A" using `square B c e d \<and> oppo_side d B c A \<and> parallelogram B c e d` by blast
	have "triangle A B c" using triangle_b[OF `\<not> col A B c`] .
	have "oppo_side g B A c" using oppositesideflip[OF `oppo_side g A B c`] .
	have "oppo_side h c A B" using oppositesideflip[OF `oppo_side h A c B`] .
	have "oppo_side d c B A" using oppositesideflip[OF `oppo_side d B c A`] .
	obtain l m where "parallelogram B m l d \<and> bet B m c \<and> parallelogram m c e l \<and> bet d l e \<and> qua_eq_area A B f g B m l d \<and> qua_eq_area A c k h m c e l" using Prop47[OF `triangle A B c` `ang_right B A c` `square A B f g` `oppo_side g B A c` `square A c k h` `oppo_side h c A B` `square B c e d` `oppo_side d c B A`]  by  blast
	have "bet B m c" using `parallelogram B m l d \<and> bet B m c \<and> parallelogram m c e l \<and> bet d l e \<and> qua_eq_area A B f g B m l d \<and> qua_eq_area A c k h m c e l` by blast
	have "parallelogram m c e l" using `parallelogram B m l d \<and> bet B m c \<and> parallelogram m c e l \<and> bet d l e \<and> qua_eq_area A B f g B m l d \<and> qua_eq_area A c k h m c e l` by blast
	have "bet d l e" using `parallelogram B m l d \<and> bet B m c \<and> parallelogram m c e l \<and> bet d l e \<and> qua_eq_area A B f g B m l d \<and> qua_eq_area A c k h m c e l` by blast
	have "qua_eq_area A B f g B m l d" using `parallelogram B m l d \<and> bet B m c \<and> parallelogram m c e l \<and> bet d l e \<and> qua_eq_area A B f g B m l d \<and> qua_eq_area A c k h m c e l` by blast
	have "qua_eq_area A c k h m c e l" using `parallelogram B m l d \<and> bet B m c \<and> parallelogram m c e l \<and> bet d l e \<and> qua_eq_area A B f g B m l d \<and> qua_eq_area A c k h m c e l` by blast
	have "seg_eq A C A c" using congruencesymmetric[OF `seg_eq A c A C`] .
	have "qua_eq_area A C K H A c k h" using squaresequal[OF `seg_eq A C A c` `square A C K H` `square A c k h`] .
	have "seg_eq A B A B" using congruencereflexiveE.
	have "qua_eq_area A B F G A B f g" using squaresequal[OF `seg_eq A B A B` `square A B F G` `square A B f g`] .
	have "qua_eq_area A B F G B m l d" using EFtransitiveE[OF `qua_eq_area A B F G A B f g` `qua_eq_area A B f g B m l d`] .
	have "qua_eq_area B M L D A B F G" using EFsymmetricE[OF `qua_eq_area A B F G B M L D`] .
	have "qua_eq_area B M L D B m l d" using EFtransitiveE[OF `qua_eq_area B M L D A B F G` `qua_eq_area A B F G B m l d`] .
	have "qua_eq_area M C E L A C K H" using EFsymmetricE[OF `qua_eq_area A C K H M C E L`] .
	have "qua_eq_area M C E L A c k h" using EFtransitiveE[OF `qua_eq_area M C E L A C K H` `qua_eq_area A C K H A c k h`] .
	have "qua_eq_area M C E L m c e l" using EFtransitiveE[OF `qua_eq_area M C E L A c k h` `qua_eq_area A c k h m c e l`] .
	have "bet e l d" using betweennesssymmetryE[OF `bet d l e`] .
	have "ang_right B c e" using square_f[OF `square B c e d`] by blast
	have "m \<noteq> c" using betweennotequal[OF `bet B m c`] by blast
	have "col B m c" using collinear_b `parallelogram B m l d \<and> bet B m c \<and> parallelogram m c e l \<and> bet d l e \<and> qua_eq_area A B f g B m l d \<and> qua_eq_area A c k h m c e l` by blast
	have "col B c m" using collinearorder[OF `col B m c`] by blast
	have "ang_right m c e" using collinearright[OF `ang_right B c e` `col B c m` `m \<noteq> c`] .
	have "parallelogram c e l m" using PGrotate[OF `parallelogram m c e l`] .
	have "rectangle c e l m" using PGrectangle[OF `parallelogram c e l m` `ang_right m c e`] .
	have "rectangle e l m c" using rectanglerotate[OF `rectangle c e l m`] .
	have "rectangle l m c e" using rectanglerotate[OF `rectangle e l m c`] .
	have "rectangle m c e l" using rectanglerotate[OF `rectangle l m c e`] .
	have "qua_eq_area B C E D B c e d" using paste5[OF `qua_eq_area B M L D B m l d` `qua_eq_area M C E L m c e l` `bet B M C` `bet B m c` `bet E L D` `bet e l d` `rectangle M C E L` `rectangle m c e l`] .
	have "seg_eq B C B c" using Prop48A[OF `square B C E D` `square B c e d` `qua_eq_area B C E D B c e d`] .
	have "seg_eq A C A c" using congruencesymmetric[OF `seg_eq A c A C`] .
	have "triangle A B c" using triangle_b[OF `\<not> col A B c`] .
	have "ang_eq B A C B A c" using Prop08[OF `triangle A B C` `triangle A B c` `seg_eq A B A B` `seg_eq A C A c` `seg_eq B C B c`] by blast
	have "ang_right B A C" using equaltorightisright[OF `ang_right B A c` `ang_eq B A C B A c`] .
	thus ?thesis by blast
qed

end