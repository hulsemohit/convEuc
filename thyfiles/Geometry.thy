
theory Geometry
	imports Main Complex_Main
begin

locale point_circ=
 fixes 
	bet :: "'point \<Rightarrow> 'point \<Rightarrow> 'point \<Rightarrow> bool" and
	seg_eq :: "'point \<Rightarrow> 'point \<Rightarrow> 'point \<Rightarrow> 'point \<Rightarrow> bool" and
	circle :: "'circ \<Rightarrow> 'point \<Rightarrow> 'point \<Rightarrow> 'point \<Rightarrow> bool"
begin                                                       
definition col where
	"col A B C \<equiv> A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B"

definition equilateral where
	"equilateral A B C \<equiv> seg_eq A B B C \<and> seg_eq B C C A"

definition triangle where
	"triangle A B C \<equiv> \<not> col A B C"

definition ray_on where
	"ray_on A B C \<equiv> \<exists> X. bet X A C \<and> bet X A B"

definition seg_lt where
	"seg_lt A B C D \<equiv> \<exists> X. bet C X D \<and> seg_eq C X A B"

definition midpoint where
	"midpoint A B C \<equiv> bet A B C \<and> seg_eq A B B C"

definition ang_eq where
	"ang_eq A B C a b c \<equiv> \<exists> U V u v. ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C"

definition supplement where
	"supplement A B C D F \<equiv> ray_on B C D \<and> bet A B F"

definition ang_right where
	"ang_right A B C \<equiv> \<exists> X. bet A B X \<and> seg_eq A B X B \<and> seg_eq A C X C \<and> B \<noteq> C"

definition perp_at where
	"perp_at P Q A B C \<equiv> \<exists> X. col P Q C \<and> col A B C \<and> col A B X \<and> ang_right X C P"

definition perp where
	"perp P Q A B \<equiv> \<exists> X. perp_at P Q A B X"

definition ang_in where
	"ang_in A B C P \<equiv> \<exists> X Y. ray_on B A X \<and> ray_on B C Y \<and> bet X P Y"

definition oppo_side where
	"oppo_side P A B Q \<equiv> \<exists> X. bet P X Q \<and> col A B X \<and> \<not> col A B P"

definition same_side where
	"same_side P Q A B \<equiv> \<exists> U V X. col A B U \<and> col A B V \<and> bet P U X \<and> bet Q V X \<and> \<not> col A B P \<and> \<not> col A B Q"

definition tri_isos where
	"tri_isos A B C \<equiv> triangle A B C \<and> seg_eq A B A C"

definition cuts where
	"cuts A B C D E \<equiv> bet A E B \<and> bet C E D \<and> \<not> col A B C \<and> \<not> col A B D"

definition tri_cong where
	"tri_cong A B C a b c \<equiv> seg_eq A B a b \<and> seg_eq B C b c \<and> seg_eq A C a c \<and> triangle A B C"

definition ang_lt where
	"ang_lt A B C D E F \<equiv> \<exists> U V X. bet U X V \<and> ray_on E D U \<and> ray_on E F V \<and> ang_eq A B C D E X"

definition seg_sum_gt where
	"seg_sum_gt A B C D E F \<equiv> \<exists> X. bet A B X \<and> seg_eq B X C D \<and> seg_lt E F A X"

definition seg_sum_pair_gt where
	"seg_sum_pair_gt A B C D E F G H \<equiv> \<exists> X. bet E F X \<and> seg_eq F X G H \<and> seg_sum_gt A B C D E X"

definition ang_sum_right where
	"ang_sum_right A B C D E F \<equiv> \<exists> U V X Y Z. supplement X Y U V Z \<and> ang_eq A B C X Y U \<and> ang_eq D E F V Y Z"

definition meets where
	"meets A B C D \<equiv> \<exists> X. A \<noteq> B \<and> C \<noteq> D \<and> col A B X \<and> col C D X"

definition cross where
	"cross A B C D \<equiv> \<exists> X. bet A X B \<and> bet C X D"

definition tarski_parallel where
	"tarski_parallel A B C D \<equiv> A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B"

definition parallel where
	"parallel A B C D \<equiv> \<exists> U V X u v. A \<noteq> B \<and> C \<noteq> D \<and> col A B U \<and> col A B V \<and> U \<noteq> V \<and> col C D u \<and> col C D v \<and> u \<noteq> v \<and> \<not> (meets A B C D) \<and> bet U X v \<and> bet u X V"

definition area_sum_eq where
	"area_sum_eq A B C D E F P Q R \<equiv> \<exists> X. ang_eq A B C P Q X \<and> ang_eq D E F X Q R \<and> bet P X R"

definition parallelogram where
	"parallelogram A B C D \<equiv> parallel A B C D \<and> parallel A D B C"

definition square where
	"square A B C D \<equiv> seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A"

definition rectangle where
	"rectangle A B C D \<equiv> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D"

definition rec_cong where
	"rec_cong A B C D a b c d \<equiv> rectangle A B C D \<and> rectangle a b c d \<and> seg_eq A B a b \<and> seg_eq B C b c"

definition rec_eq_area where
	"rec_eq_area A B C D a b c d \<equiv> \<exists> U W X Y Z u w x z. rec_cong A B C D X Y Z U \<and> rec_cong a b c d x Y z u \<and> bet x Y Z \<and> bet X Y z \<and> bet W U w"

definition base_rect where
	"base_rect A B C D E \<equiv> rectangle B C D E \<and> col D E A"

definition figure_rect where
	"figure_rect A B C D E F G H \<equiv> rectangle E F G H \<and> bet E B F \<and> bet H D G \<and> base_rect C B D G F \<and> base_rect A B D H E"

definition tri_eq_area where
	"tri_eq_area A B C a b c \<equiv> \<exists> X Y x y. rectangle A B X Y \<and> rectangle a b x y \<and> col X Y C \<and> col x y c \<and> rec_eq_area A B X Y a b x y"

definition qua_eq_area where
	"qua_eq_area A B C D a b c d \<equiv> \<exists> U X Y Z u x y z. oppo_side A B C D \<and> oppo_side a b c d \<and> figure_rect A B C D X Y Z U \<and> figure_rect a b c d x y z u \<and> rec_eq_area X Y Z U x y z u"

definition cir_in where
	"cir_in P J \<equiv> (\<exists> A B C X Y. circle J C A B \<and> bet X C Y \<and> seg_eq C Y A B \<and> seg_eq C X A B \<and> bet X P Y)"

definition cir_ou where
	"cir_ou P J \<equiv> (\<exists> A B C X. circle J C A B \<and> bet C X P \<and> seg_eq C X A B)"

definition cir_on where
	"cir_on B J \<equiv> (\<exists> A C D. circle J A C D \<and> seg_eq A B C D)"


definition n5_line where
	"n5_line \<equiv> \<forall> A B C D a b c d. seg_eq B C b c \<and> seg_eq A D a d \<and> seg_eq B D b d \<and> bet A B C \<and> bet a b c \<and> seg_eq A B a b \<longrightarrow> (seg_eq D C d c)"

definition EFpermutation where
	"EFpermutation \<equiv> \<forall> A B C D a b c d. qua_eq_area A B C D a b c d \<longrightarrow> (qua_eq_area A B C D b c d a \<and> qua_eq_area A B C D d c b a \<and> qua_eq_area A B C D c d a b \<and> qua_eq_area A B C D b a d c \<and> qua_eq_area A B C D d a b c \<and> qua_eq_area A B C D c b a d \<and> qua_eq_area A B C D a d c b)"

definition EFsymmetric where
	"EFsymmetric \<equiv> \<forall> A B C D a b c d. qua_eq_area A B C D a b c d \<longrightarrow> (qua_eq_area a b c d A B C D)"

definition EFtransitive where
	"EFtransitive \<equiv> \<forall> A B C D P Q R S a b c d. qua_eq_area A B C D a b c d \<and> qua_eq_area a b c d P Q R S \<longrightarrow> (qua_eq_area A B C D P Q R S)"

definition ETpermutation where
	"ETpermutation \<equiv> \<forall> A B C a b c. tri_eq_area A B C a b c \<longrightarrow> (tri_eq_area A B C b c a \<and> tri_eq_area A B C a c b \<and> tri_eq_area A B C b a c \<and> tri_eq_area A B C c b a \<and> tri_eq_area A B C c a b)"

definition ETsymmetric where
	"ETsymmetric \<equiv> \<forall> A B C a b c. tri_eq_area A B C a b c \<longrightarrow> (tri_eq_area a b c A B C)"

definition ETtransitive where
	"ETtransitive \<equiv> \<forall> A B C P Q R a b c. tri_eq_area A B C a b c \<and> tri_eq_area a b c P Q R \<longrightarrow> (tri_eq_area A B C P Q R)"

definition Euclid5 where
	"Euclid5 \<equiv> \<forall> a p q r s t. bet r t s \<and> bet p t q \<and> bet r a q \<and> seg_eq p t q t \<and> seg_eq t r t s \<longrightarrow> (\<exists> X. bet p a X \<and> bet s q X)"

definition Pasch_inner where
	"Pasch_inner \<equiv> \<forall> A B C P Q. bet A P C \<and> bet B Q C \<and> \<not> col A C B \<longrightarrow> (\<exists> X. bet A X Q \<and> bet B X P)"

definition Pasch_outer where
	"Pasch_outer \<equiv> \<forall> A B C P Q. bet A P C \<and> bet B C Q \<and> \<not> col B Q A \<longrightarrow> (\<exists> X. bet A X Q \<and> bet B P X)"

definition betweennessidentity where
	"betweennessidentity \<equiv> \<forall> A B. \<not> (bet A B A)"

definition betweennesssymmetry where
	"betweennesssymmetry \<equiv> \<forall> A B C. bet A B C \<longrightarrow> (bet C B A)"

definition circle_circle where
	"circle_circle \<equiv> \<forall> C D F G J K P Q R S. circle J C R S \<and> cir_in P J \<and> cir_ou Q J \<and> circle K D F G \<and> cir_on P K \<and> cir_on Q K \<longrightarrow> (\<exists> X. cir_on X J \<and> cir_on X K)"

definition congruencereflexive where
	"congruencereflexive \<equiv> \<forall> A B. seg_eq A B A B"

definition congruencetransitive where
	"congruencetransitive \<equiv> \<forall> B C D E P Q. seg_eq P Q B C \<and> seg_eq P Q D E \<longrightarrow> (seg_eq B C D E)"

definition congruentequal where
	"congruentequal \<equiv> \<forall> A B C a b c. tri_cong A B C a b c \<longrightarrow> (tri_eq_area A B C a b c)"

definition connectivity where
	"connectivity \<equiv> \<forall> A B C D. bet A B D \<and> bet A C D \<and> \<not> (bet A B C) \<and> \<not> (bet A C B) \<longrightarrow> (B = C)"

definition cutoff1 where
	"cutoff1 \<equiv> \<forall> A B C D E a b c d e. bet A B C \<and> bet a b c \<and> bet E D C \<and> bet e d c \<and> tri_eq_area B C D b c d \<and> tri_eq_area A C E a c e \<longrightarrow> (qua_eq_area A B D E a b d e)"

definition cutoff2 where
	"cutoff2 \<equiv> \<forall> A B C D E a b c d e. bet B C D \<and> bet b c d \<and> tri_eq_area C D E c d e \<and> qua_eq_area A B D E a b d e \<longrightarrow> (qua_eq_area A B C E a b c e)"

definition deZolt1 where
	"deZolt1 \<equiv> \<forall> B C D E. bet B E D \<longrightarrow> (\<not> (tri_eq_area D B C E B C))"

definition deZolt2 where
	"deZolt2 \<equiv> \<forall> A B C E F. triangle A B C \<and> bet B E A \<and> bet B F C \<longrightarrow> (\<not> (tri_eq_area A B C E B F))"

definition equalityreverse where
	"equalityreverse \<equiv> \<forall> A B. seg_eq A B B A"

definition extension where
	"extension \<equiv> \<forall> A B C D. A \<noteq> B \<and> C \<noteq> D \<longrightarrow> (\<exists> X. bet A B X \<and> seg_eq B X C D)"

definition halvesofequals where
	"halvesofequals \<equiv> \<forall> A B C D a b c d. tri_eq_area A B C B C D \<and> oppo_side A B C D \<and> tri_eq_area a b c b c d \<and> oppo_side a b c d \<and> qua_eq_area A B D C a b d c \<longrightarrow> (tri_eq_area A B C a b c)"

definition innertransitivity where
	"innertransitivity \<equiv> \<forall> A B C D. bet A B D \<and> bet B C D \<longrightarrow> (bet A B C)"

definition line_circle where
	"line_circle \<equiv> \<forall> A B C K P Q. circle K C P Q \<and> cir_in B K \<and> A \<noteq> B \<longrightarrow> (\<exists> X Y. col A B X \<and> col A B Y \<and> cir_on X K \<and> cir_on Y K \<and> bet X B Y)"

definition nullsegment1 where
	"nullsegment1 \<equiv> \<forall> A B C. seg_eq A B C C \<longrightarrow> (A = B)"

definition nullsegment2 where
	"nullsegment2 \<equiv> \<forall> A B. seg_eq A A B B"

definition paste1 where
	"paste1 \<equiv> \<forall> A B C D E a b c d e. bet A B C \<and> bet a b c \<and> bet E D C \<and> bet e d c \<and> tri_eq_area B C D b c d \<and> qua_eq_area A B D E a b d e \<longrightarrow> (tri_eq_area A C E a c e)"

definition paste2 where
	"paste2 \<equiv> \<forall> A B C D E M a b c d e m. bet B C D \<and> bet b c d \<and> tri_eq_area C D E c d e \<and> qua_eq_area A B C E a b c e \<and> bet A M D \<and> bet B M E \<and> bet a m d \<and> bet b m e \<longrightarrow> (qua_eq_area A B D E a b d e)"

definition paste3 where
	"paste3 \<equiv> \<forall> A B C D M a b c d m. tri_eq_area A B C a b c \<and>
    tri_eq_area A B D a b d \<and> bet C M D \<and> (bet A M B \<or> A = M \<or> M = B)
    \<and> bet c m d \<and> (bet a m b \<or> a = m \<or> m = b) \<longrightarrow> (qua_eq_area A C B D a c b d)"

definition paste4 where
	"paste4 \<equiv> \<forall> A B C D F G H J K L M P e m. qua_eq_area A B m D F K H G \<and> qua_eq_area D B e C G H M L \<and> bet A P C \<and> bet B P D \<and> bet K H M \<and> bet F G L \<and> bet B m D \<and> bet B e C \<and> bet F J M \<and> bet K J L \<longrightarrow> (qua_eq_area A B C D F K M L)"


definition circle_ne where
	"circle_ne \<equiv> \<forall> A B C.(\<exists> X. circle X C A B) \<longleftrightarrow> A \<noteq> B"

definition circle_unique where
 "circle_unique \<equiv> \<forall> J A B C X Y Z. circle J A B C \<and> circle J X Y Z \<longrightarrow> A = X \<and> seg_eq B C Y Z"

definition axioms where
	"axioms \<equiv> n5_line \<and> EFpermutation \<and> EFsymmetric \<and> EFtransitive \<and> ETpermutation \<and> ETsymmetric \<and> ETtransitive \<and> Euclid5 \<and> Pasch_inner \<and> Pasch_outer \<and> betweennessidentity \<and> betweennesssymmetry \<and> circle_circle \<and> congruencereflexive \<and> congruencetransitive \<and> congruentequal \<and> connectivity \<and> cutoff1 \<and> cutoff2 \<and> deZolt1 \<and> deZolt2 \<and> equalityreverse \<and> extension \<and> halvesofequals \<and> innertransitivity \<and> line_circle \<and> nullsegment1 \<and> nullsegment2 \<and> paste1 \<and> paste2 \<and> paste3 \<and> paste4 \<and> circle_ne \<and> circle_unique"
end

locale euclidean_geometry = point_circ + assumes ax:"point_circ.axioms bet seg_eq circle"

lemma(in euclidean_geometry) anglelessthan_b:
	assumes
		"bet U X V"
		"ray_on E D U"
		"ray_on E F V"
		"ang_eq A B C D E X"
	shows "ang_lt A B C D E F"
	using assms ang_lt_def by fastforce

lemma(in euclidean_geometry) anglelessthan_f:
	assumes
		"ang_lt A B C D E F"
	shows "\<exists> U V X. bet U X V \<and> ray_on E D U \<and> ray_on E F V \<and> ang_eq A B C D E X"
	using assms ang_lt_def by fastforce

lemma(in euclidean_geometry) anglesum_b:
	assumes
		"ang_eq A B C P Q X"
		"ang_eq D E F X Q R"
		"bet P X R"
	shows "area_sum_eq A B C D E F P Q R"
	using assms area_sum_eq_def by fastforce

lemma(in euclidean_geometry) anglesum_f:
	assumes
		"area_sum_eq A B C D E F P Q R"
	shows "\<exists> X. ang_eq A B C P Q X \<and> ang_eq D E F X Q R \<and> bet P X R"
	using assms area_sum_eq_def by fastforce

lemma(in euclidean_geometry) baserectangle_b:
	assumes
		"rectangle B C D E"
		"col D E A"
	shows "base_rect A B C D E"
	using assms base_rect_def by fastforce

lemma(in euclidean_geometry) baserectangle_f:
	assumes
		"base_rect A B C D E"
	shows "rectangle B C D E \<and> col D E A"
	using assms base_rect_def by fastforce

lemma(in euclidean_geometry) circle_b:
	assumes
		"circle X C A B"
	shows "A \<noteq> B"
using assms ax axioms_def circle_ne_def by fastforce
 

lemma(in euclidean_geometry) circle_f:
	assumes
		"A \<noteq> B"
	shows "\<forall> C. \<exists> X. circle X C A B"
	using assms ax axioms_def circle_ne_def by fastforce

lemma(in euclidean_geometry) collinear_b:
	assumes
		"A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B"
	shows "col A B C"
	using assms col_def by fastforce

lemma(in euclidean_geometry) collinear_f:
	assumes
		"col A B C"
	shows "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B"
	using assms col_def by fastforce

lemma(in euclidean_geometry) congruentrectangles_b:
	assumes
		"rectangle A B C D"
		"rectangle a b c d"
		"seg_eq A B a b"
		"seg_eq B C b c"
	shows "rec_cong A B C D a b c d"
	using assms ax axioms_def rec_cong_def by fastforce

lemma(in euclidean_geometry) congruentrectangles_f:
	assumes
		"rec_cong A B C D a b c d"
	shows "rectangle A B C D \<and> rectangle a b c d \<and> seg_eq A B a b \<and> seg_eq B C b c"
	using assms rec_cong_def by fastforce

lemma(in euclidean_geometry) cross_b:
	assumes
		"bet A X B"
		"bet C X D"
	shows "cross A B C D"
	using assms cross_def by fastforce

lemma(in euclidean_geometry) cross_f:
	assumes
		"cross A B C D"
	shows "\<exists> X. bet A X B \<and> bet C X D"
	using assms cross_def by fastforce

lemma(in euclidean_geometry) cut_b:
	assumes
		"bet A E B"
		"bet C E D"
		"\<not> col A B C"
		"\<not> col A B D"
	shows "cuts A B C D E"
	using assms cuts_def by fastforce

lemma(in euclidean_geometry) cut_f:
	assumes
		"cuts A B C D E"
	shows "bet A E B \<and> bet C E D \<and> \<not> col A B C \<and> \<not> col A B D"
	using assms cuts_def by fastforce

lemma(in euclidean_geometry) equalangles_b:
	assumes
		"ray_on B A U"
		"ray_on B C V"
		"ray_on b a u"
		"ray_on b c v"
		"seg_eq B U b u"
		"seg_eq B V b v"
		"seg_eq U V u v"
		"\<not> col A B C"
	shows "ang_eq A B C a b c"
	using assms ang_eq_def by fastforce

lemma(in euclidean_geometry) equalangles_f:
	assumes
		"ang_eq A B C a b c"
	shows "\<exists> U V u v. ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C"
	using assms ang_eq_def by fastforce

lemma(in euclidean_geometry) equalfigures_b:
	assumes
		"oppo_side A B C D"
		"oppo_side a b c d"
		"figure_rect A B C D X Y Z U"
		"figure_rect a b c d x y z u"
		"rec_eq_area X Y Z U x y z u"
	shows "qua_eq_area A B C D a b c d"
	using assms qua_eq_area_def by fastforce

lemma(in euclidean_geometry) equalfigures_f:
	assumes
		"qua_eq_area A B C D a b c d"
	shows "\<exists> U X Y Z u x y z. oppo_side A B C D \<and> oppo_side a b c d \<and> figure_rect A B C D X Y Z U \<and> figure_rect a b c d x y z u \<and> rec_eq_area X Y Z U x y z u"
	using assms qua_eq_area_def by fastforce

lemma(in euclidean_geometry) equalrectangles_b:
	assumes
		"rec_cong A B C D X Y Z U"
		"rec_cong a b c d x Y z u"
		"bet x Y Z"
		"bet X Y z"
		"bet W U w"
	shows "rec_eq_area A B C D a b c d"
	using assms rec_eq_area_def by fastforce

lemma(in euclidean_geometry) equalrectangles_f:
	assumes
		"rec_eq_area A B C D a b c d"
	shows "\<exists> U W X Y Z u w x z. rec_cong A B C D X Y Z U \<and> rec_cong a b c d x Y z u \<and> bet x Y Z \<and> bet X Y z \<and> bet W U w"
	using assms rec_eq_area_def by fastforce

lemma(in euclidean_geometry) equaltriangles_b:
	assumes
		"rectangle A B X Y"
		"rectangle a b x y"
		"col X Y C"
		"col x y c"
		"rec_eq_area A B X Y a b x y"
	shows "tri_eq_area A B C a b c"
	using assms tri_eq_area_def by fastforce

lemma(in euclidean_geometry) equaltriangles_f:
	assumes
		"tri_eq_area A B C a b c"
	shows "\<exists> X Y x y. rectangle A B X Y \<and> rectangle a b x y \<and> col X Y C \<and> col x y c \<and> rec_eq_area A B X Y a b x y"
	using assms tri_eq_area_def by fastforce

lemma(in euclidean_geometry) equilateral_b:
	assumes
		"seg_eq A B B C"
		"seg_eq B C C A"
	shows "equilateral A B C"
	using assms equilateral_def by fastforce

lemma(in euclidean_geometry) equilateral_f:
	assumes
		"equilateral A B C"
	shows "seg_eq A B B C \<and> seg_eq B C C A"
	using assms equilateral_def by fastforce

lemma(in euclidean_geometry) figurerectangle_b:
	assumes
		"rectangle E F G H"
		"bet E B F"
		"bet H D G"
		"base_rect C B D G F"
		"base_rect A B D H E"
	shows "figure_rect A B C D E F G H"
	using assms figure_rect_def by fastforce

lemma(in euclidean_geometry) figurerectangle_f:
	assumes
		"figure_rect A B C D E F G H"
	shows "rectangle E F G H \<and> bet E B F \<and> bet H D G \<and> base_rect C B D G F \<and> base_rect A B D H E"
	using assms figure_rect_def by fastforce

lemma(in euclidean_geometry) inside_b:
	assumes
		"circle J C A B"
		"bet X C Y"
		"seg_eq C Y A B"
		"seg_eq C X A B"
		"bet X P Y"
	shows "circle J C A B \<and> cir_in P J"
	using assms cir_in_def by fastforce

lemma(in euclidean_geometry) inside_f:
	assumes
		"circle J C A B"
		"cir_in P J"
	shows "\<exists> X Y. circle J C A B \<and> bet X C Y \<and> seg_eq C Y A B \<and> seg_eq C X A B \<and> bet X P Y"
proof -
 obtain U V W X Y where "circle J U V W" "bet X U Y" "seg_eq U Y V W" "seg_eq U X V W" "bet X P Y" using assms cir_in_def by blast
 have "U = C" using ax axioms_def `circle J U V W` `circle J C A B` circle_unique_def by blast
 have "bet X C Y" using `U = C` `bet X U Y` by simp
 have "seg_eq V W A B" using ax axioms_def `circle J U V W` `circle J C A B` ax circle_unique_def by blast
 have "seg_eq C X A B" using ax axioms_def `seg_eq U X V W` `seg_eq V W A B` `U = C` congruencetransitive_def congruencereflexive_def by metis
 have "seg_eq C Y A B" using ax axioms_def `seg_eq U Y V W` `seg_eq V W A B` `U = C` congruencetransitive_def congruencereflexive_def by metis
 show ?thesis using `bet X C Y` `bet X P Y` `seg_eq C X A B` `seg_eq C Y A B` `circle J C A B` by blast
qed

lemma(in euclidean_geometry) interior_b:
	assumes
		"ray_on B A X"
		"ray_on B C Y"
		"bet X P Y"
	shows "ang_in A B C P"
	using assms ang_in_def by fastforce

lemma(in euclidean_geometry) interior_f:
	assumes
		"ang_in A B C P"
	shows "\<exists> X Y. ray_on B A X \<and> ray_on B C Y \<and> bet X P Y"
	using assms ang_in_def by fastforce

lemma(in euclidean_geometry) isosceles_b:
	assumes
		"triangle A B C"
		"seg_eq A B A C"
	shows "tri_isos A B C"
	using assms tri_isos_def by fastforce

lemma(in euclidean_geometry) isosceles_f:
	assumes
		"tri_isos A B C"
	shows "triangle A B C \<and> seg_eq A B A C"
	using assms tri_isos_def by fastforce

lemma(in euclidean_geometry) lessthan_b:
	assumes
		"bet C X D"
		"seg_eq C X A B"
	shows "seg_lt A B C D"
	using assms seg_lt_def by fastforce

lemma(in euclidean_geometry) lessthan_f:
	assumes
		"seg_lt A B C D"
	shows "\<exists> X. bet C X D \<and> seg_eq C X A B"
	using assms seg_lt_def by fastforce

lemma(in euclidean_geometry) meet_b:
	assumes
		"A \<noteq> B"
		"C \<noteq> D"
		"col A B X"
		"col C D X"
	shows "meets A B C D"
	using assms meets_def by fastforce

lemma(in euclidean_geometry) meet_f:
	assumes
		"meets A B C D"
	shows "\<exists> X. A \<noteq> B \<and> C \<noteq> D \<and> col A B X \<and> col C D X"
	using assms meets_def by fastforce

lemma(in euclidean_geometry) midpoint_b:
	assumes
		"bet A B C"
		"seg_eq A B B C"
	shows "midpoint A B C"
	using assms midpoint_def by fastforce

lemma(in euclidean_geometry) midpoint_f:
	assumes
		"midpoint A B C"
	shows "bet A B C \<and> seg_eq A B B C"
	using assms midpoint_def by fastforce

lemma(in euclidean_geometry) on_b:
	assumes
		"circle J A C D"
		"seg_eq A B C D"
	shows "circle J A C D \<and> cir_on B J"
	using assms cir_on_def by fastforce

lemma(in euclidean_geometry) on_f:
	assumes
		"circle J A C D"
		"cir_on B J"
	shows "circle J A C D \<and> seg_eq A B C D"
proof -
 obtain X Y Z where "circle J X Y Z" "seg_eq X B Y Z" using assms cir_on_def by blast
 have "X = A" using ax axioms_def circle_unique_def `circle J X Y Z` `circle J A C D` axioms_def by blast
 have "seg_eq C D Y Z" using ax axioms_def assms circle_unique_def `circle J X Y Z` `circle J A C D` by blast
 have "seg_eq X B C D" using ax axioms_def congruencetransitive_def congruencereflexive_def `seg_eq C D Y Z` `seg_eq X B Y Z` by metis
 have "seg_eq A B C D" using `seg_eq X B C D` `X = A` by simp
 thus ?thesis using `circle J A C D` by simp
qed

lemma(in euclidean_geometry) oppositeside_b:
	assumes
		"bet P X Q"
		"col A B X"
		"\<not> col A B P"
	shows "oppo_side P A B Q"
	using assms oppo_side_def by fastforce

lemma(in euclidean_geometry) oppositeside_f:
	assumes
		"oppo_side P A B Q"
	shows "\<exists> X. bet P X Q \<and> col A B X \<and> \<not> col A B P"
	using assms oppo_side_def by fastforce

lemma(in euclidean_geometry) outside_b:
	assumes
		"circle J C A B"
		"bet C X P"
		"seg_eq C X A B"
	shows "circle J C A B \<and> cir_ou P J"
	using assms cir_ou_def by fastforce

lemma(in euclidean_geometry) outside_f:
	assumes
		"circle J C A B"
		"cir_ou P J"
	shows "\<exists> X. circle J C A B \<and> bet C X P \<and> seg_eq C X A B"
proof -
 obtain U V W X where "circle J U V W" "bet U X P" "seg_eq U X V W" using `cir_ou P J` cir_ou_def by blast
 have "U = C" using ax `circle J U V W` `circle J C A B`  axioms_def circle_unique_def by blast
 have "bet C X P" using `bet U X P` `U = C` by blast
 have "seg_eq V W A B" using ax `circle J U V W` `circle J C A B`  axioms_def circle_unique_def by blast
 have "seg_eq U X A B" using  ax axioms_def congruencetransitive_def congruencereflexive_def `seg_eq U X V W` `seg_eq V W A B` by metis
 have "seg_eq C X A B" using `seg_eq U X A B` `U = C` by simp
 show ?thesis using \<open>bet C X P\<close> \<open>seg_eq C X A B\<close> `circle J C A B` by blast
qed

lemma(in euclidean_geometry) parallel_b:
	assumes
		"A \<noteq> B"
		"C \<noteq> D"
		"col A B U"
		"col A B V"
		"U \<noteq> V"
		"col C D u"
		"col C D v"
		"u \<noteq> v"
		"\<not> (meets A B C D)"
		"bet U X v"
		"bet u X V"
	shows "parallel A B C D"
	using assms parallel_def by fastforce

lemma(in euclidean_geometry) parallel_f:
	assumes
		"parallel A B C D"
	shows "\<exists> U V X u v. A \<noteq> B \<and> C \<noteq> D \<and> col A B U \<and> col A B V \<and> U \<noteq> V \<and> col C D u \<and> col C D v \<and> u \<noteq> v \<and> \<not> (meets A B C D) \<and> bet U X v \<and> bet u X V"
	using assms parallel_def by fastforce

lemma(in euclidean_geometry) parallelogram_b:
	assumes
		"parallel A B C D"
		"parallel A D B C"
	shows "parallelogram A B C D"
	using assms parallelogram_def by fastforce

lemma(in euclidean_geometry) parallelogram_f:
	assumes
		"parallelogram A B C D"
	shows "parallel A B C D \<and> parallel A D B C"
	using assms parallelogram_def by fastforce

lemma(in euclidean_geometry) perpat_b:
	assumes
		"col P Q C"
		"col A B C"
		"col A B X"
		"ang_right X C P"
	shows "perp_at P Q A B C"
	using assms perp_at_def by fastforce

lemma(in euclidean_geometry) perpat_f:
	assumes
		"perp_at P Q A B C"
	shows "\<exists> X. col P Q C \<and> col A B C \<and> col A B X \<and> ang_right X C P"
	using assms perp_at_def by fastforce

lemma(in euclidean_geometry) perpendicular_b:
	assumes
		"perp_at P Q A B X"
	shows "perp P Q A B"
	using assms perp_def by fastforce

lemma(in euclidean_geometry) perpendicular_f:
	assumes
		"perp P Q A B"
	shows "\<exists> X. perp_at P Q A B X"
	using assms perp_def by fastforce

lemma(in euclidean_geometry) ray_b:
	assumes
		"bet X A C"
		"bet X A B"
	shows "ray_on A B C"
	using assms ray_on_def by fastforce

lemma(in euclidean_geometry) ray_f:
	assumes
		"ray_on A B C"
	shows "\<exists> X. bet X A C \<and> bet X A B"
	using assms ray_on_def by fastforce

lemma(in euclidean_geometry) rectangle_b:
	assumes
		"ang_right D A B"
		"ang_right A B C"
		"ang_right B C D"
		"ang_right C D A"
		"cross A C B D"
	shows "rectangle A B C D"
	using assms rectangle_def by fastforce

lemma(in euclidean_geometry) rectangle_f:
	assumes
		"rectangle A B C D"
	shows "ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D"
	using assms rectangle_def by fastforce

lemma(in euclidean_geometry) rightangle_b:
	assumes
		"bet A B X"
		"seg_eq A B X B"
		"seg_eq A C X C"
		"B \<noteq> C"
	shows "ang_right A B C"
	using assms ang_right_def by fastforce

lemma(in euclidean_geometry) rightangle_f:
	assumes
		"ang_right A B C"
	shows "\<exists> X. bet A B X \<and> seg_eq A B X B \<and> seg_eq A C X C \<and> B \<noteq> C"
	using assms ang_right_def by fastforce

lemma(in euclidean_geometry) sameside_b:
	assumes
		"col A B U"
		"col A B V"
		"bet P U X"
		"bet Q V X"
		"\<not> col A B P"
		"\<not> col A B Q"
	shows "same_side P Q A B"
	using assms same_side_def by fastforce

lemma(in euclidean_geometry) sameside_f:
	assumes
		"same_side P Q A B"
	shows "\<exists> U V X. col A B U \<and> col A B V \<and> bet P U X \<and> bet Q V X \<and> \<not> col A B P \<and> \<not> col A B Q"
	using assms same_side_def by fastforce

lemma(in euclidean_geometry) square_b:
	assumes
		"seg_eq A B C D"
		"seg_eq A B B C"
		"seg_eq A B D A"
		"ang_right D A B"
		"ang_right A B C"
		"ang_right B C D"
		"ang_right C D A"
	shows "square A B C D"
	using assms square_def by fastforce

lemma(in euclidean_geometry) square_f:
	assumes
		"square A B C D"
	shows "seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A"
	using assms square_def by fastforce

lemma(in euclidean_geometry) supplement_b:
	assumes
		"ray_on B C D"
		"bet A B F"
	shows "supplement A B C D F"
	using assms supplement_def by fastforce

lemma(in euclidean_geometry) supplement_f:
	assumes
		"supplement A B C D F"
	shows "ray_on B C D \<and> bet A B F"
	using assms supplement_def by fastforce

lemma(in euclidean_geometry) tarski_parallel_b:
	assumes
		"A \<noteq> B"
		"C \<noteq> D"
		"\<not> (meets A B C D)"
		"same_side C D A B"
	shows "tarski_parallel A B C D"
	using assms tarski_parallel_def by fastforce

lemma(in euclidean_geometry) tarski_parallel_f:
	assumes
		"tarski_parallel A B C D"
	shows "A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B"
	using assms tarski_parallel_def by fastforce

lemma(in euclidean_geometry) togetherfour_b:
	assumes
		"bet E F X"
		"seg_eq F X G H"
		"seg_sum_gt A B C D E X"
	shows "seg_sum_pair_gt A B C D E F G H"
	using assms seg_sum_pair_gt_def by fastforce

lemma(in euclidean_geometry) togetherfour_f:
	assumes
		"seg_sum_pair_gt A B C D E F G H"
	shows "\<exists> X. bet E F X \<and> seg_eq F X G H \<and> seg_sum_gt A B C D E X"
	using assms seg_sum_pair_gt_def by fastforce

lemma(in euclidean_geometry) togethergreater_b:
	assumes
		"bet A B X"
		"seg_eq B X C D"
		"seg_lt E F A X"
	shows "seg_sum_gt A B C D E F"
	using assms seg_sum_gt_def by fastforce

lemma(in euclidean_geometry) togethergreater_f:
	assumes
		"seg_sum_gt A B C D E F"
	shows "\<exists> X. bet A B X \<and> seg_eq B X C D \<and> seg_lt E F A X"
	using assms seg_sum_gt_def by fastforce

lemma(in euclidean_geometry) triangle_b:
	assumes
		"\<not> col A B C"
	shows "triangle A B C"
	using assms triangle_def by fastforce

lemma(in euclidean_geometry) triangle_f:
	assumes
		"triangle A B C"
	shows "\<not> col A B C"
	using assms triangle_def by fastforce

lemma(in euclidean_geometry) trianglecongruence_b:
	assumes
		"seg_eq A B a b"
		"seg_eq B C b c"
		"seg_eq A C a c"
		"triangle A B C"
	shows "tri_cong A B C a b c"
	using assms tri_cong_def by fastforce

lemma(in euclidean_geometry) trianglecongruence_f:
	assumes
		"tri_cong A B C a b c"
	shows "seg_eq A B a b \<and> seg_eq B C b c \<and> seg_eq A C a c \<and> triangle A B C"
	using assms tri_cong_def by fastforce

lemma(in euclidean_geometry) tworightangles_b:
	assumes
		"supplement X Y U V Z"
		"ang_eq A B C X Y U"
		"ang_eq D E F V Y Z"
	shows "ang_sum_right A B C D E F"
	using assms ang_sum_right_def by fastforce

lemma(in euclidean_geometry) tworightangles_f:
	assumes
		"ang_sum_right A B C D E F"
	shows "\<exists> U V X Y Z. supplement X Y U V Z \<and> ang_eq A B C X Y U \<and> ang_eq D E F V Y Z"
	using assms ang_sum_right_def by fastforce


lemma(in euclidean_geometry) n5_lineE:
	assumes
		"seg_eq B C b c"
		"seg_eq A D a d"
		"seg_eq B D b d"
		"bet A B C"
		"bet a b c"
		"seg_eq A B a b"
	shows "seg_eq D C d c"
	using assms ax axioms_def n5_line_def by blast

lemma(in euclidean_geometry) EFpermutationE:
	assumes
		"qua_eq_area A B C D a b c d"
	shows "qua_eq_area A B C D b c d a \<and> qua_eq_area A B C D d c b a \<and> qua_eq_area A B C D c d a b \<and> qua_eq_area A B C D b a d c \<and> qua_eq_area A B C D d a b c \<and> qua_eq_area A B C D c b a d \<and> qua_eq_area A B C D a d c b"
	using assms ax axioms_def EFpermutation_def by blast

lemma(in euclidean_geometry) EFsymmetricE:
	assumes
		"qua_eq_area A B C D a b c d"
	shows "qua_eq_area a b c d A B C D"
	using assms ax axioms_def EFsymmetric_def by blast

lemma(in euclidean_geometry) EFtransitiveE:
	assumes
		"qua_eq_area A B C D a b c d"
		"qua_eq_area a b c d P Q R S"
	shows "qua_eq_area A B C D P Q R S"
	using assms ax axioms_def EFtransitive_def by blast

lemma(in euclidean_geometry) ETpermutationE:
	assumes
		"tri_eq_area A B C a b c"
	shows "tri_eq_area A B C b c a \<and> tri_eq_area A B C a c b \<and> tri_eq_area A B C b a c \<and> tri_eq_area A B C c b a \<and> tri_eq_area A B C c a b"
	using assms ax axioms_def ETpermutation_def by blast

lemma(in euclidean_geometry) ETsymmetricE:
	assumes
		"tri_eq_area A B C a b c"
	shows "tri_eq_area a b c A B C"
	using assms ax axioms_def ETsymmetric_def by blast

lemma(in euclidean_geometry) ETtransitiveE:
	assumes
		"tri_eq_area A B C a b c"
		"tri_eq_area a b c P Q R"
	shows "tri_eq_area A B C P Q R"
	using assms ax axioms_def ETtransitive_def by blast

lemma(in euclidean_geometry) Euclid5E:
	assumes
		"bet r t s"
		"bet p t q"
		"bet r a q"
		"seg_eq p t q t"
		"seg_eq t r t s"
	shows "\<exists> X. bet p a X \<and> bet s q X"
	using assms ax axioms_def Euclid5_def by blast

lemma(in euclidean_geometry) Pasch_innerE:
	assumes
		"bet A P C"
		"bet B Q C"
		"\<not> col A C B"
	shows "\<exists> X. bet A X Q \<and> bet B X P"
	using assms ax axioms_def Pasch_inner_def by blast

lemma(in euclidean_geometry) Pasch_outerE:
	assumes
		"bet A P C"
		"bet B C Q"
		"\<not> col B Q A"
	shows "\<exists> X. bet A X Q \<and> bet B P X"
	using assms ax axioms_def Pasch_outer_def by blast

lemma(in euclidean_geometry) betweennessidentityE:
	shows "\<not> (bet A B A)"
	using ax axioms_def betweennessidentity_def by blast

lemma(in euclidean_geometry) betweennesssymmetryE:
	assumes
		"bet A B C"
	shows "bet C B A"
	using assms ax axioms_def betweennesssymmetry_def by blast

lemma(in euclidean_geometry) circle_circleE:
	assumes 
		"circle J C R S"
		"cir_in P J"
		"cir_ou Q J"
		"circle K D F G"
		"cir_on P K"
		"cir_on Q K"
	shows "\<exists> X. cir_on X J \<and> cir_on X K"
	using assms ax axioms_def circle_circle_def by blast

lemma(in euclidean_geometry) congruencereflexiveE:
	shows "seg_eq A B A B"
	using ax axioms_def congruencereflexive_def by blast

lemma(in euclidean_geometry) congruencetransitiveE:
	assumes
		"seg_eq P Q B C"
		"seg_eq P Q D E"
	shows "seg_eq B C D E"
	using assms ax axioms_def congruencetransitive_def by blast

lemma(in euclidean_geometry) congruentequalE:
	assumes
		"tri_cong A B C a b c"
	shows "tri_eq_area A B C a b c"
	using assms ax axioms_def congruentequal_def by blast

lemma(in euclidean_geometry) connectivityE:
	assumes
		"bet A B D"
		"bet A C D"
		"\<not> (bet A B C)"
		"\<not> (bet A C B)"
	shows "B = C"
	using assms ax axioms_def connectivity_def by blast

lemma(in euclidean_geometry) cutoff1E:
	assumes
		"bet A B C"
		"bet a b c"
		"bet E D C"
		"bet e d c"
		"tri_eq_area B C D b c d"
		"tri_eq_area A C E a c e"
	shows "qua_eq_area A B D E a b d e"
	using assms ax axioms_def cutoff1_def by blast

lemma(in euclidean_geometry) cutoff2E:
	assumes
		"bet B C D"
		"bet b c d"
		"tri_eq_area C D E c d e"
		"qua_eq_area A B D E a b d e"
	shows "qua_eq_area A B C E a b c e"
	using assms ax axioms_def cutoff2_def by blast

lemma(in euclidean_geometry) deZolt1E:
	assumes
		"bet B E D"
	shows "\<not> (tri_eq_area D B C E B C)"
	using assms ax axioms_def deZolt1_def by blast

lemma(in euclidean_geometry) deZolt2E:
	assumes
		"triangle A B C"
		"bet B E A"
		"bet B F C"
	shows "\<not> (tri_eq_area A B C E B F)"
	using assms ax axioms_def deZolt2_def by blast

lemma(in euclidean_geometry) equalityreflexiveE:
	shows "A = A"
 by blast

lemma(in euclidean_geometry) equalityreverseE:
	shows "seg_eq A B B A"
	using ax axioms_def equalityreverse_def by blast

lemma(in euclidean_geometry) equalitytransitiveE:
	assumes
		"A = C"
		"B = C"
	shows "A = B"
 using assms by blast

lemma(in euclidean_geometry) extensionE:
	assumes
		"A \<noteq> B"
		"C \<noteq> D"
	shows "\<exists> X. bet A B X \<and> seg_eq B X C D"
	using assms ax axioms_def extension_def by blast

lemma(in euclidean_geometry) halvesofequalsE:
	assumes
		"tri_eq_area A B C B C D"
		"oppo_side A B C D"
		"tri_eq_area a b c b c d"
		"oppo_side a b c d"
		"qua_eq_area A B D C a b d c"
	shows "tri_eq_area A B C a b c"
	using assms ax axioms_def halvesofequals_def by blast

lemma(in euclidean_geometry) innertransitivityE:
	assumes
		"bet A B D"
		"bet B C D"
	shows "bet A B C"
	using assms ax axioms_def innertransitivity_def by blast

lemma(in euclidean_geometry) line_circleE:
	assumes
		"circle K C P Q"
		"cir_in B K"
		"A \<noteq> B"
	shows "\<exists> X Y. col A B X \<and> col A B Y \<and> cir_on X K \<and> cir_on Y K \<and> bet X B Y"
	using assms ax axioms_def line_circle_def by blast

lemma(in euclidean_geometry) nullsegment1E:
	assumes
		"seg_eq A B C C"
	shows "A = B"
	using assms ax axioms_def nullsegment1_def by blast

lemma(in euclidean_geometry) nullsegment2E:
	shows "seg_eq A A B B"
 using ax axioms_def nullsegment2_def by blast

lemma(in euclidean_geometry) paste1E:
	assumes
		"bet A B C"
		"bet a b c"
		"bet E D C"
		"bet e d c"
		"tri_eq_area B C D b c d"
		"qua_eq_area A B D E a b d e"
	shows "tri_eq_area A C E a c e"
	using assms ax axioms_def paste1_def by blast

lemma(in euclidean_geometry) paste2E:
	assumes
		"bet B C D"
		"bet b c d"
		"tri_eq_area C D E c d e"
		"qua_eq_area A B C E a b c e"
		"bet A M D"
		"bet B M E"
		"bet a m d"
		"bet b m e"
	shows "qua_eq_area A B D E a b d e"
	using assms ax axioms_def paste2_def by blast

lemma(in euclidean_geometry) paste3E:
	assumes
		"tri_eq_area A B C a b c"
		"tri_eq_area A B D a b d"
		"bet C M D"
		"bet A M B \<or> A = M \<or> M = B"
		"bet c m d"
		"bet a m b \<or> a = m \<or> m = b"
	shows "qua_eq_area A C B D a c b d"
	using assms ax axioms_def paste3_def by blast

lemma(in euclidean_geometry) paste4E:
	assumes
		"qua_eq_area A B m D F K H G"
		"qua_eq_area D B e C G H M L"
		"bet A P C"
		"bet B P D"
		"bet K H M"
		"bet F G L"
		"bet B m D"
		"bet B e C"
		"bet F J M"
		"bet K J L"
	shows "qua_eq_area A B C D F K M L"
	using assms ax axioms_def paste4_def by blast

lemma(in euclidean_geometry) stabilityE:
	assumes
		"\<not> (A \<noteq> B)"
	shows "A = B"
	using assms ax axioms_def by blast
end

