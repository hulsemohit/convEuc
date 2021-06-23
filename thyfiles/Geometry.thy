theory Geometry
	imports Main
begin

typedecl point
typedecl circ

consts
	bet :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool"
	seg_eq :: "point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool"
	circle :: "circ \<Rightarrow> point \<Rightarrow> point \<Rightarrow> point \<Rightarrow> bool"

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
	"cir_in P J \<equiv> \<forall> C A B. circle J C A B \<longrightarrow> (\<exists> X Y. circle J C A B \<and> bet X C Y \<and> seg_eq C Y A B \<and> seg_eq C X A B \<and> bet X P Y)"

definition cir_ou where
	"cir_ou P J \<equiv> \<forall> C A B. circle J C A B \<longrightarrow> (\<exists> X. circle J C A B \<and> bet C X P \<and> seg_eq C X A B)"

definition cir_on where
	"cir_on B J \<equiv> \<forall> A C D. circle J A C D \<longrightarrow> circle J A C D \<and> seg_eq A B C D"


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
	"betweennessidentity \<equiv> \<forall> A B :: point. \<not> (bet A B A)"

definition betweennesssymmetry where
	"betweennesssymmetry \<equiv> \<forall> A B C. bet A B C \<longrightarrow> (bet C B A)"

definition circle_circle where
	"circle_circle \<equiv> \<forall> C D F G J K P Q R S. circle J C R S \<and> cir_in P J \<and> cir_ou Q J \<and> circle K D F G \<and> cir_on P K \<and> cir_on Q K \<longrightarrow> (\<exists> X. cir_on X J \<and> cir_on X K)"

definition congruencereflexive where
	"congruencereflexive \<equiv> \<forall> A B :: point. seg_eq A B A B"

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

definition equalityreflexive where
	"equalityreflexive \<equiv> \<forall> A :: point. A = A"

definition equalityreverse where
	"equalityreverse \<equiv> \<forall> A B :: point. seg_eq A B B A"

definition equalitytransitive where
	"equalitytransitive \<equiv> \<forall> A B C :: point. A = C \<and> B = C \<longrightarrow> (A = B)"

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
	"nullsegment2 \<equiv> \<forall> A B :: point. seg_eq A A B B"

definition paste1 where
	"paste1 \<equiv> \<forall> A B C D E a b c d e. bet A B C \<and> bet a b c \<and> bet E D C \<and> bet e d c \<and> tri_eq_area B C D b c d \<and> qua_eq_area A B D E a b d e \<longrightarrow> (tri_eq_area A C E a c e)"

definition paste2 where
	"paste2 \<equiv> \<forall> A B C D E M a b c d e m. bet B C D \<and> bet b c d \<and> tri_eq_area C D E c d e \<and> qua_eq_area A B C E a b c e \<and> bet A M D \<and> bet B M E \<and> bet a m d \<and> bet b m e \<longrightarrow> (qua_eq_area A B D E a b d e)"

definition paste3 where
	"paste3 \<equiv> \<forall> A B C D M a b c d m. tri_eq_area A B C a b c \<and> tri_eq_area A B D a b d \<and> bet C M D \<and> bet A M B \<or> A = M \<or> M = B \<and> bet c m d \<and> bet a m b \<or> a = m \<or> m = b \<longrightarrow> (qua_eq_area A C B D a c b d)"

definition paste4 where
	"paste4 \<equiv> \<forall> A B C D F G H J K L M P e m. qua_eq_area A B m D F K H G \<and> qua_eq_area D B e C G H M L \<and> bet A P C \<and> bet B P D \<and> bet K H M \<and> bet F G L \<and> bet B m D \<and> bet B e C \<and> bet F J M \<and> bet K J L \<longrightarrow> (qua_eq_area A B C D F K M L)"

definition stability where
	"stability \<equiv> \<forall> A B :: point. \<not> (A \<noteq> B) \<longrightarrow> (A = B)"

definition circle_ne where
	"circle_ne \<equiv> \<forall> A B C.(\<exists> X. circle X C A B) \<longleftrightarrow> A \<noteq> B"

definition axioms where
	"axioms \<equiv> n5_line \<and> EFpermutation \<and> EFsymmetric \<and> EFtransitive \<and> ETpermutation \<and> ETsymmetric \<and> ETtransitive \<and> Euclid5 \<and> Pasch_inner \<and> Pasch_outer \<and> betweennessidentity \<and> betweennesssymmetry \<and> circle_circle \<and> congruencereflexive \<and> congruencetransitive \<and> congruentequal \<and> connectivity \<and> cutoff1 \<and> cutoff2 \<and> deZolt1 \<and> deZolt2 \<and> equalityreflexive \<and> equalityreverse \<and> equalitytransitive \<and> extension \<and> halvesofequals \<and> innertransitivity \<and> line_circle \<and> nullsegment1 \<and> nullsegment2 \<and> paste1 \<and> paste2 \<and> paste3 \<and> paste4 \<and> stability \<and> circle_ne"

lemma anglelessthan_b:
	assumes "axioms"
		"bet U X V"
		"ray_on E D U"
		"ray_on E F V"
		"ang_eq A B C D E X"
	shows "ang_lt A B C D E F"
	using assms axioms_def ang_lt_def by fastforce

lemma anglelessthan_f:
	assumes "axioms"
		"ang_lt A B C D E F"
	shows "\<exists> U V X. bet U X V \<and> ray_on E D U \<and> ray_on E F V \<and> ang_eq A B C D E X"
	using assms axioms_def ang_lt_def by fastforce

lemma anglesum_b:
	assumes "axioms"
		"ang_eq A B C P Q X"
		"ang_eq D E F X Q R"
		"bet P X R"
	shows "area_sum_eq A B C D E F P Q R"
	using assms axioms_def area_sum_eq_def by fastforce

lemma anglesum_f:
	assumes "axioms"
		"area_sum_eq A B C D E F P Q R"
	shows "\<exists> X. ang_eq A B C P Q X \<and> ang_eq D E F X Q R \<and> bet P X R"
	using assms axioms_def area_sum_eq_def by fastforce

lemma baserectangle_b:
	assumes "axioms"
		"rectangle B C D E"
		"col D E A"
	shows "base_rect A B C D E"
	using assms axioms_def base_rect_def by fastforce

lemma baserectangle_f:
	assumes "axioms"
		"base_rect A B C D E"
	shows "rectangle B C D E \<and> col D E A"
	using assms axioms_def base_rect_def by fastforce

lemma circle_b:
	assumes "axioms"
		"circle X C A B"
	shows "A \<noteq> B"
	using assms axioms_def circle_ne_def by fastforce

lemma circle_f:
	assumes "axioms"
		"A \<noteq> B"
	shows "\<forall> C. \<exists> X. circle X C A B"
	using assms axioms_def circle_ne_def by fastforce

lemma collinear_b:
	assumes "axioms"
		"A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B"
	shows "col A B C"
	using assms axioms_def col_def by fastforce

lemma collinear_f:
	assumes "axioms"
		"col A B C"
	shows "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B"
	using assms axioms_def col_def by fastforce

lemma congruentrectangles_b:
	assumes "axioms"
		"rectangle A B C D"
		"rectangle a b c d"
		"seg_eq A B a b"
		"seg_eq B C b c"
	shows "rec_cong A B C D a b c d"
	using assms axioms_def rec_cong_def by fastforce

lemma congruentrectangles_f:
	assumes "axioms"
		"rec_cong A B C D a b c d"
	shows "rectangle A B C D \<and> rectangle a b c d \<and> seg_eq A B a b \<and> seg_eq B C b c"
	using assms axioms_def rec_cong_def by fastforce

lemma cross_b:
	assumes "axioms"
		"bet A X B"
		"bet C X D"
	shows "cross A B C D"
	using assms axioms_def cross_def by fastforce

lemma cross_f:
	assumes "axioms"
		"cross A B C D"
	shows "\<exists> X. bet A X B \<and> bet C X D"
	using assms axioms_def cross_def by fastforce

lemma cut_b:
	assumes "axioms"
		"bet A E B"
		"bet C E D"
		"\<not> col A B C"
		"\<not> col A B D"
	shows "cuts A B C D E"
	using assms axioms_def cuts_def by fastforce

lemma cut_f:
	assumes "axioms"
		"cuts A B C D E"
	shows "bet A E B \<and> bet C E D \<and> \<not> col A B C \<and> \<not> col A B D"
	using assms axioms_def cuts_def by fastforce

lemma equalangles_b:
	assumes "axioms"
		"ray_on B A U"
		"ray_on B C V"
		"ray_on b a u"
		"ray_on b c v"
		"seg_eq B U b u"
		"seg_eq B V b v"
		"seg_eq U V u v"
		"\<not> col A B C"
	shows "ang_eq A B C a b c"
	using assms axioms_def ang_eq_def by fastforce

lemma equalangles_f:
	assumes "axioms"
		"ang_eq A B C a b c"
	shows "\<exists> U V u v. ray_on B A U \<and> ray_on B C V \<and> ray_on b a u \<and> ray_on b c v \<and> seg_eq B U b u \<and> seg_eq B V b v \<and> seg_eq U V u v \<and> \<not> col A B C"
	using assms axioms_def ang_eq_def by fastforce

lemma equalfigures_b:
	assumes "axioms"
		"oppo_side A B C D"
		"oppo_side a b c d"
		"figure_rect A B C D X Y Z U"
		"figure_rect a b c d x y z u"
		"rec_eq_area X Y Z U x y z u"
	shows "qua_eq_area A B C D a b c d"
	using assms axioms_def qua_eq_area_def by fastforce

lemma equalfigures_f:
	assumes "axioms"
		"qua_eq_area A B C D a b c d"
	shows "\<exists> U X Y Z u x y z. oppo_side A B C D \<and> oppo_side a b c d \<and> figure_rect A B C D X Y Z U \<and> figure_rect a b c d x y z u \<and> rec_eq_area X Y Z U x y z u"
	using assms axioms_def qua_eq_area_def by fastforce

lemma equalrectangles_b:
	assumes "axioms"
		"rec_cong A B C D X Y Z U"
		"rec_cong a b c d x Y z u"
		"bet x Y Z"
		"bet X Y z"
		"bet W U w"
	shows "rec_eq_area A B C D a b c d"
	using assms axioms_def rec_eq_area_def by fastforce

lemma equalrectangles_f:
	assumes "axioms"
		"rec_eq_area A B C D a b c d"
	shows "\<exists> U W X Y Z u w x z. rec_cong A B C D X Y Z U \<and> rec_cong a b c d x Y z u \<and> bet x Y Z \<and> bet X Y z \<and> bet W U w"
	using assms axioms_def rec_eq_area_def by fastforce

lemma equaltriangles_b:
	assumes "axioms"
		"rectangle A B X Y"
		"rectangle a b x y"
		"col X Y C"
		"col x y c"
		"rec_eq_area A B X Y a b x y"
	shows "tri_eq_area A B C a b c"
	using assms axioms_def tri_eq_area_def by fastforce

lemma equaltriangles_f:
	assumes "axioms"
		"tri_eq_area A B C a b c"
	shows "\<exists> X Y x y. rectangle A B X Y \<and> rectangle a b x y \<and> col X Y C \<and> col x y c \<and> rec_eq_area A B X Y a b x y"
	using assms axioms_def tri_eq_area_def by fastforce

lemma equilateral_b:
	assumes "axioms"
		"seg_eq A B B C"
		"seg_eq B C C A"
	shows "equilateral A B C"
	using assms axioms_def equilateral_def by fastforce

lemma equilateral_f:
	assumes "axioms"
		"equilateral A B C"
	shows "seg_eq A B B C \<and> seg_eq B C C A"
	using assms axioms_def equilateral_def by fastforce

lemma figurerectangle_b:
	assumes "axioms"
		"rectangle E F G H"
		"bet E B F"
		"bet H D G"
		"base_rect C B D G F"
		"base_rect A B D H E"
	shows "figure_rect A B C D E F G H"
	using assms axioms_def figure_rect_def by fastforce

lemma figurerectangle_f:
	assumes "axioms"
		"figure_rect A B C D E F G H"
	shows "rectangle E F G H \<and> bet E B F \<and> bet H D G \<and> base_rect C B D G F \<and> base_rect A B D H E"
	using assms axioms_def figure_rect_def by fastforce

lemma inside_b:
	assumes "axioms"
		"circle J C A B"
		"bet X C Y"
		"seg_eq C Y A B"
		"seg_eq C X A B"
		"bet X P Y"
	shows "circle J C A B \<and> cir_in P J"
	using assms axioms_def cir_in_def sorry

lemma inside_f:
	assumes "axioms"
		"circle J C A B"
		"cir_in P J"
	shows "\<exists> X Y. circle J C A B \<and> bet X C Y \<and> seg_eq C Y A B \<and> seg_eq C X A B \<and> bet X P Y"
	using assms axioms_def cir_in_def by fastforce

lemma interior_b:
	assumes "axioms"
		"ray_on B A X"
		"ray_on B C Y"
		"bet X P Y"
	shows "ang_in A B C P"
	using assms axioms_def ang_in_def by fastforce

lemma interior_f:
	assumes "axioms"
		"ang_in A B C P"
	shows "\<exists> X Y. ray_on B A X \<and> ray_on B C Y \<and> bet X P Y"
	using assms axioms_def ang_in_def by fastforce

lemma isosceles_b:
	assumes "axioms"
		"triangle A B C"
		"seg_eq A B A C"
	shows "tri_isos A B C"
	using assms axioms_def tri_isos_def by fastforce

lemma isosceles_f:
	assumes "axioms"
		"tri_isos A B C"
	shows "triangle A B C \<and> seg_eq A B A C"
	using assms axioms_def tri_isos_def by fastforce

lemma lessthan_b:
	assumes "axioms"
		"bet C X D"
		"seg_eq C X A B"
	shows "seg_lt A B C D"
	using assms axioms_def seg_lt_def by fastforce

lemma lessthan_f:
	assumes "axioms"
		"seg_lt A B C D"
	shows "\<exists> X. bet C X D \<and> seg_eq C X A B"
	using assms axioms_def seg_lt_def by fastforce

lemma meet_b:
	assumes "axioms"
		"A \<noteq> B"
		"C \<noteq> D"
		"col A B X"
		"col C D X"
	shows "meets A B C D"
	using assms axioms_def meets_def by fastforce

lemma meet_f:
	assumes "axioms"
		"meets A B C D"
	shows "\<exists> X. A \<noteq> B \<and> C \<noteq> D \<and> col A B X \<and> col C D X"
	using assms axioms_def meets_def by fastforce

lemma midpoint_b:
	assumes "axioms"
		"bet A B C"
		"seg_eq A B B C"
	shows "midpoint A B C"
	using assms axioms_def midpoint_def by fastforce

lemma midpoint_f:
	assumes "axioms"
		"midpoint A B C"
	shows "bet A B C \<and> seg_eq A B B C"
	using assms axioms_def midpoint_def by fastforce

lemma on_b:
	assumes "axioms"
		"circle J A C D"
		"seg_eq A B C D"
	shows "circle J A C D \<and> cir_on B J"
	using assms axioms_def cir_on_def sorry

lemma on_f:
	assumes "axioms"
		"circle J A C D"
		"cir_on B J"
	shows "circle J A C D \<and> seg_eq A B C D"
	using assms axioms_def cir_on_def by fastforce

lemma oppositeside_b:
	assumes "axioms"
		"bet P X Q"
		"col A B X"
		"\<not> col A B P"
	shows "oppo_side P A B Q"
	using assms axioms_def oppo_side_def by fastforce

lemma oppositeside_f:
	assumes "axioms"
		"oppo_side P A B Q"
	shows "\<exists> X. bet P X Q \<and> col A B X \<and> \<not> col A B P"
	using assms axioms_def oppo_side_def by fastforce

lemma outside_b:
	assumes "axioms"
		"circle J C A B"
		"bet C X P"
		"seg_eq C X A B"
	shows "circle J C A B \<and> cir_ou P J"
	using assms axioms_def cir_ou_def sorry

lemma outside_f:
	assumes "axioms"
		"circle J C A B"
		"cir_ou P J"
	shows "\<exists> X. circle J C A B \<and> bet C X P \<and> seg_eq C X A B"
	using assms axioms_def cir_ou_def by fastforce

lemma parallel_b:
	assumes "axioms"
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
	using assms axioms_def parallel_def by fastforce

lemma parallel_f:
	assumes "axioms"
		"parallel A B C D"
	shows "\<exists> U V X u v. A \<noteq> B \<and> C \<noteq> D \<and> col A B U \<and> col A B V \<and> U \<noteq> V \<and> col C D u \<and> col C D v \<and> u \<noteq> v \<and> \<not> (meets A B C D) \<and> bet U X v \<and> bet u X V"
	using assms axioms_def parallel_def by fastforce

lemma parallelogram_b:
	assumes "axioms"
		"parallel A B C D"
		"parallel A D B C"
	shows "parallelogram A B C D"
	using assms axioms_def parallelogram_def by fastforce

lemma parallelogram_f:
	assumes "axioms"
		"parallelogram A B C D"
	shows "parallel A B C D \<and> parallel A D B C"
	using assms axioms_def parallelogram_def by fastforce

lemma perpat_b:
	assumes "axioms"
		"col P Q C"
		"col A B C"
		"col A B X"
		"ang_right X C P"
	shows "perp_at P Q A B C"
	using assms axioms_def perp_at_def by fastforce

lemma perpat_f:
	assumes "axioms"
		"perp_at P Q A B C"
	shows "\<exists> X. col P Q C \<and> col A B C \<and> col A B X \<and> ang_right X C P"
	using assms axioms_def perp_at_def by fastforce

lemma perpendicular_b:
	assumes "axioms"
		"perp_at P Q A B X"
	shows "perp P Q A B"
	using assms axioms_def perp_def by fastforce

lemma perpendicular_f:
	assumes "axioms"
		"perp P Q A B"
	shows "\<exists> X. perp_at P Q A B X"
	using assms axioms_def perp_def by fastforce

lemma ray_b:
	assumes "axioms"
		"bet X A C"
		"bet X A B"
	shows "ray_on A B C"
	using assms axioms_def ray_on_def by fastforce

lemma ray_f:
	assumes "axioms"
		"ray_on A B C"
	shows "\<exists> X. bet X A C \<and> bet X A B"
	using assms axioms_def ray_on_def by fastforce

lemma rectangle_b:
	assumes "axioms"
		"ang_right D A B"
		"ang_right A B C"
		"ang_right B C D"
		"ang_right C D A"
		"cross A C B D"
	shows "rectangle A B C D"
	using assms axioms_def rectangle_def by fastforce

lemma rectangle_f:
	assumes "axioms"
		"rectangle A B C D"
	shows "ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D"
	using assms axioms_def rectangle_def by fastforce

lemma rightangle_b:
	assumes "axioms"
		"bet A B X"
		"seg_eq A B X B"
		"seg_eq A C X C"
		"B \<noteq> C"
	shows "ang_right A B C"
	using assms axioms_def ang_right_def by fastforce

lemma rightangle_f:
	assumes "axioms"
		"ang_right A B C"
	shows "\<exists> X. bet A B X \<and> seg_eq A B X B \<and> seg_eq A C X C \<and> B \<noteq> C"
	using assms axioms_def ang_right_def by fastforce

lemma sameside_b:
	assumes "axioms"
		"col A B U"
		"col A B V"
		"bet P U X"
		"bet Q V X"
		"\<not> col A B P"
		"\<not> col A B Q"
	shows "same_side P Q A B"
	using assms axioms_def same_side_def by fastforce

lemma sameside_f:
	assumes "axioms"
		"same_side P Q A B"
	shows "\<exists> U V X. col A B U \<and> col A B V \<and> bet P U X \<and> bet Q V X \<and> \<not> col A B P \<and> \<not> col A B Q"
	using assms axioms_def same_side_def by fastforce

lemma square_b:
	assumes "axioms"
		"seg_eq A B C D"
		"seg_eq A B B C"
		"seg_eq A B D A"
		"ang_right D A B"
		"ang_right A B C"
		"ang_right B C D"
		"ang_right C D A"
	shows "square A B C D"
	using assms axioms_def square_def by fastforce

lemma square_f:
	assumes "axioms"
		"square A B C D"
	shows "seg_eq A B C D \<and> seg_eq A B B C \<and> seg_eq A B D A \<and> ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A"
	using assms axioms_def square_def by fastforce

lemma supplement_b:
	assumes "axioms"
		"ray_on B C D"
		"bet A B F"
	shows "supplement A B C D F"
	using assms axioms_def supplement_def by fastforce

lemma supplement_f:
	assumes "axioms"
		"supplement A B C D F"
	shows "ray_on B C D \<and> bet A B F"
	using assms axioms_def supplement_def by fastforce

lemma tarski_parallel_b:
	assumes "axioms"
		"A \<noteq> B"
		"C \<noteq> D"
		"\<not> (meets A B C D)"
		"same_side C D A B"
	shows "tarski_parallel A B C D"
	using assms axioms_def tarski_parallel_def by fastforce

lemma tarski_parallel_f:
	assumes "axioms"
		"tarski_parallel A B C D"
	shows "A \<noteq> B \<and> C \<noteq> D \<and> \<not> (meets A B C D) \<and> same_side C D A B"
	using assms axioms_def tarski_parallel_def by fastforce

lemma togetherfour_b:
	assumes "axioms"
		"bet E F X"
		"seg_eq F X G H"
		"seg_sum_gt A B C D E X"
	shows "seg_sum_pair_gt A B C D E F G H"
	using assms axioms_def seg_sum_pair_gt_def by fastforce

lemma togetherfour_f:
	assumes "axioms"
		"seg_sum_pair_gt A B C D E F G H"
	shows "\<exists> X. bet E F X \<and> seg_eq F X G H \<and> seg_sum_gt A B C D E X"
	using assms axioms_def seg_sum_pair_gt_def by fastforce

lemma togethergreater_b:
	assumes "axioms"
		"bet A B X"
		"seg_eq B X C D"
		"seg_lt E F A X"
	shows "seg_sum_gt A B C D E F"
	using assms axioms_def seg_sum_gt_def by fastforce

lemma togethergreater_f:
	assumes "axioms"
		"seg_sum_gt A B C D E F"
	shows "\<exists> X. bet A B X \<and> seg_eq B X C D \<and> seg_lt E F A X"
	using assms axioms_def seg_sum_gt_def by fastforce

lemma triangle_b:
	assumes "axioms"
		"\<not> col A B C"
	shows "triangle A B C"
	using assms axioms_def triangle_def by fastforce

lemma triangle_f:
	assumes "axioms"
		"triangle A B C"
	shows "\<not> col A B C"
	using assms axioms_def triangle_def by fastforce

lemma trianglecongruence_b:
	assumes "axioms"
		"seg_eq A B a b"
		"seg_eq B C b c"
		"seg_eq A C a c"
		"triangle A B C"
	shows "tri_cong A B C a b c"
	using assms axioms_def tri_cong_def by fastforce

lemma trianglecongruence_f:
	assumes "axioms"
		"tri_cong A B C a b c"
	shows "seg_eq A B a b \<and> seg_eq B C b c \<and> seg_eq A C a c \<and> triangle A B C"
	using assms axioms_def tri_cong_def by fastforce

lemma tworightangles_b:
	assumes "axioms"
		"supplement X Y U V Z"
		"ang_eq A B C X Y U"
		"ang_eq D E F V Y Z"
	shows "ang_sum_right A B C D E F"
	using assms axioms_def ang_sum_right_def by fastforce

lemma tworightangles_f:
	assumes "axioms"
		"ang_sum_right A B C D E F"
	shows "\<exists> U V X Y Z. supplement X Y U V Z \<and> ang_eq A B C X Y U \<and> ang_eq D E F V Y Z"
	using assms axioms_def ang_sum_right_def by fastforce


lemma n5_lineE:
	assumes "axioms"
		"seg_eq B C b c"
		"seg_eq A D a d"
		"seg_eq B D b d"
		"bet A B C"
		"bet a b c"
		"seg_eq A B a b"
	shows "seg_eq D C d c"
	using assms axioms_def n5_line_def by blast

lemma EFpermutationE:
	assumes "axioms"
		"qua_eq_area A B C D a b c d"
	shows "qua_eq_area A B C D b c d a \<and> qua_eq_area A B C D d c b a \<and> qua_eq_area A B C D c d a b \<and> qua_eq_area A B C D b a d c \<and> qua_eq_area A B C D d a b c \<and> qua_eq_area A B C D c b a d \<and> qua_eq_area A B C D a d c b"
	using assms axioms_def EFpermutation_def by blast

lemma EFsymmetricE:
	assumes "axioms"
		"qua_eq_area A B C D a b c d"
	shows "qua_eq_area a b c d A B C D"
	using assms axioms_def EFsymmetric_def by blast

lemma EFtransitiveE:
	assumes "axioms"
		"qua_eq_area A B C D a b c d"
		"qua_eq_area a b c d P Q R S"
	shows "qua_eq_area A B C D P Q R S"
	using assms axioms_def EFtransitive_def by blast

lemma ETpermutationE:
	assumes "axioms"
		"tri_eq_area A B C a b c"
	shows "tri_eq_area A B C b c a \<and> tri_eq_area A B C a c b \<and> tri_eq_area A B C b a c \<and> tri_eq_area A B C c b a \<and> tri_eq_area A B C c a b"
	using assms axioms_def ETpermutation_def by blast

lemma ETsymmetricE:
	assumes "axioms"
		"tri_eq_area A B C a b c"
	shows "tri_eq_area a b c A B C"
	using assms axioms_def ETsymmetric_def by blast

lemma ETtransitiveE:
	assumes "axioms"
		"tri_eq_area A B C a b c"
		"tri_eq_area a b c P Q R"
	shows "tri_eq_area A B C P Q R"
	using assms axioms_def ETtransitive_def by blast

lemma Euclid5E:
	assumes "axioms"
		"bet r t s"
		"bet p t q"
		"bet r a q"
		"seg_eq p t q t"
		"seg_eq t r t s"
	shows "\<exists> X. bet p a X \<and> bet s q X"
	using assms axioms_def Euclid5_def by blast

lemma Pasch_innerE:
	assumes "axioms"
		"bet A P C"
		"bet B Q C"
		"\<not> col A C B"
	shows "\<exists> X. bet A X Q \<and> bet B X P"
	using assms axioms_def Pasch_inner_def by blast

lemma Pasch_outerE:
	assumes "axioms"
		"bet A P C"
		"bet B C Q"
		"\<not> col B Q A"
	shows "\<exists> X. bet A X Q \<and> bet B P X"
	using assms axioms_def Pasch_outer_def by blast

lemma betweennessidentityE:
	assumes "axioms"
	shows "\<not> (bet A B A)"
	using assms axioms_def betweennessidentity_def by blast

lemma betweennesssymmetryE:
	assumes "axioms"
		"bet A B C"
	shows "bet C B A"
	using assms axioms_def betweennesssymmetry_def by blast

lemma circle_circleE:
	assumes "axioms"
		"circle J C R S"
		"cir_in P J"
		"cir_ou Q J"
		"circle K D F G"
		"cir_on P K"
		"cir_on Q K"
	shows "\<exists> X. cir_on X J \<and> cir_on X K"
	using assms axioms_def circle_circle_def by blast

lemma congruencereflexiveE:
	assumes "axioms"
	shows "seg_eq A B A B"
	using assms axioms_def congruencereflexive_def by blast

lemma congruencetransitiveE:
	assumes "axioms"
		"seg_eq P Q B C"
		"seg_eq P Q D E"
	shows "seg_eq B C D E"
	using assms axioms_def congruencetransitive_def by blast

lemma congruentequalE:
	assumes "axioms"
		"tri_cong A B C a b c"
	shows "tri_eq_area A B C a b c"
	using assms axioms_def congruentequal_def by blast

lemma connectivityE:
	assumes "axioms"
		"bet A B D"
		"bet A C D"
		"\<not> (bet A B C)"
		"\<not> (bet A C B)"
	shows "B = C"
	using assms axioms_def connectivity_def by blast

lemma cutoff1E:
	assumes "axioms"
		"bet A B C"
		"bet a b c"
		"bet E D C"
		"bet e d c"
		"tri_eq_area B C D b c d"
		"tri_eq_area A C E a c e"
	shows "qua_eq_area A B D E a b d e"
	using assms axioms_def cutoff1_def by blast

lemma cutoff2E:
	assumes "axioms"
		"bet B C D"
		"bet b c d"
		"tri_eq_area C D E c d e"
		"qua_eq_area A B D E a b d e"
	shows "qua_eq_area A B C E a b c e"
	using assms axioms_def cutoff2_def by blast

lemma deZolt1E:
	assumes "axioms"
		"bet B E D"
	shows "\<not> (tri_eq_area D B C E B C)"
	using assms axioms_def deZolt1_def by blast

lemma deZolt2E:
	assumes "axioms"
		"triangle A B C"
		"bet B E A"
		"bet B F C"
	shows "\<not> (tri_eq_area A B C E B F)"
	using assms axioms_def deZolt2_def by blast

lemma equalityreflexiveE:
	assumes "axioms"
	shows "A = A"
	using assms axioms_def equalityreflexive_def by blast

lemma equalityreverseE:
	assumes "axioms"
	shows "seg_eq A B B A"
	using assms axioms_def equalityreverse_def by blast

lemma equalitytransitiveE:
	assumes "axioms"
		"A = C"
		"B = C"
	shows "A = B"
	using assms axioms_def equalitytransitive_def by blast

lemma extensionE:
	assumes "axioms"
		"A \<noteq> B"
		"C \<noteq> D"
	shows "\<exists> X. bet A B X \<and> seg_eq B X C D"
	using assms axioms_def extension_def by blast

lemma halvesofequalsE:
	assumes "axioms"
		"tri_eq_area A B C B C D"
		"oppo_side A B C D"
		"tri_eq_area a b c b c d"
		"oppo_side a b c d"
		"qua_eq_area A B D C a b d c"
	shows "tri_eq_area A B C a b c"
	using assms axioms_def halvesofequals_def by blast

lemma innertransitivityE:
	assumes "axioms"
		"bet A B D"
		"bet B C D"
	shows "bet A B C"
	using assms axioms_def innertransitivity_def by blast

lemma line_circleE:
	assumes "axioms"
		"circle K C P Q"
		"cir_in B K"
		"A \<noteq> B"
	shows "\<exists> X Y. col A B X \<and> col A B Y \<and> cir_on X K \<and> cir_on Y K \<and> bet X B Y"
	using assms axioms_def line_circle_def by blast

lemma nullsegment1E:
	assumes "axioms"
		"seg_eq A B C C"
	shows "A = B"
	using assms axioms_def nullsegment1_def by blast

lemma nullsegment2E:
	assumes "axioms"
	shows "seg_eq A A B B"
	using assms axioms_def nullsegment2_def by blast

lemma paste1E:
	assumes "axioms"
		"bet A B C"
		"bet a b c"
		"bet E D C"
		"bet e d c"
		"tri_eq_area B C D b c d"
		"qua_eq_area A B D E a b d e"
	shows "tri_eq_area A C E a c e"
	using assms axioms_def paste1_def by blast

lemma paste2E:
	assumes "axioms"
		"bet B C D"
		"bet b c d"
		"tri_eq_area C D E c d e"
		"qua_eq_area A B C E a b c e"
		"bet A M D"
		"bet B M E"
		"bet a m d"
		"bet b m e"
	shows "qua_eq_area A B D E a b d e"
	using assms axioms_def paste2_def by blast

lemma paste3E:
	assumes "axioms"
		"tri_eq_area A B C a b c"
		"tri_eq_area A B D a b d"
		"bet C M D"
		"bet A M B \<or> A = M \<or> M = B"
		"bet c m d"
		"bet a m b \<or> a = m \<or> m = b"
	shows "qua_eq_area A C B D a c b d"
	using assms axioms_def paste3_def by blast

lemma paste4E:
	assumes "axioms"
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
	using assms axioms_def paste4_def by blast

lemma stabilityE:
	assumes "axioms"
		"\<not> (A \<noteq> B)"
	shows "A = B"
	using assms axioms_def stability_def by blast

end