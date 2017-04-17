#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX(x, y) (((x) > (y)) ? (x) : (y))
#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#define MAXINT 2147483647

struct Point {
	double x, y;
};

struct Tree {
	struct Point sp, ep;
	int si, ei;
	int li, ri;
	int level;
	double w;
};

int DEBUG = 0;
int lp[2] = {10, 10}, lt[2], cp[2] = {0, 0}, ct[2] = {0, 0};
struct Point *points[2];
struct Tree *tree[2];
double Cz;
double n;
double *u, *um, uw = 0;
struct Point *ump[2];

void help() {
	printf("Usage: dmc [input file 1] [input file 2] [Cz] [n]\n");
	printf("Parameters:\n");
	printf("   input file 1: the first input file\n");
	printf("   input file 2: the second input file\n");
	printf("   Cz:           the error of points, which is a constant\n");
	printf("   n:            segment length, divide each segment to several n-lengthed segments\n");
}

/* Segment length */
double length(struct Point s, struct Point e) {
	return sqrt((s.x-e.x)*(s.x-e.x) + (s.y-e.y)*(s.y-e.y));
}

int equal(double d1, double d2) {
	return (fabs(d1 - d2) < 0.0000001);
}

int equal(struct Point p1, struct Point p2) {
	return (equal(p1.x, p2.x) && equal(p1.y, p2.y));
}

/* cosine theta, which is the intersection angle between a & b */
double cosine(double a, double b, double c) {
	if (a == 0 || b == 0) return 0;
	return (a*a + b*b - c*c) / (2*a*b);
}

double d(struct Point s, struct Point e, struct Point c) {
	double lCurve  = length(c, s);
	double rCurve  = length(c, e);
	double seCurve = length(s, e);
	double cosTheta = (lCurve*lCurve + seCurve*seCurve - rCurve*rCurve) / (2*lCurve*seCurve);
	double d = lCurve * sin(acos(cosTheta));
	if (DEBUG) {
		printf("s(%.6lf %.6lf) e(%.6lf %.6lf) c(%.6lf %.6lf)\n", s.x, s.y, e.x, e.y, c.x, c.y);
		printf("lCurve=%.6lf rCurve=%.6lf seCurve=%.6lf cosTheta=%.6lf d=%.6lf\n", lCurve, rCurve, seCurve, cosTheta, d);
	}
	return d;
}

void split(int t, int idx) {
	if (tree[t][idx].ei - tree[t][idx].si == 1) return;

	double maxd = -1;
	int maxp;
	for (int i=tree[t][idx].si+1; i<tree[t][idx].ei; i++) {
		double dc = d(tree[t][idx].sp, tree[t][idx].ep, points[t][i]);
		if (DEBUG) printf("idx=%d i=%d d=%.6lf\n", idx, i, dc);
		if (dc > maxd) {
			maxd = dc;
			maxp = i;
		}
	}
	double ll = length(tree[t][idx].sp, points[t][maxp]);
	double lr = length(points[t][maxp], tree[t][idx].ep);

	if (ct[t] >= lt[t]) {
		lt[t] *= 2;
		tree[t] = (struct Tree*) realloc(tree[t], lt[t] * sizeof(struct Tree));
	}
	tree[t][ct[t]].sp = tree[t][idx].sp;
	tree[t][ct[t]].ep = points[t][maxp];
	tree[t][ct[t]].si = tree[t][idx].si;
	tree[t][ct[t]].ei = maxp;
	tree[t][ct[t]].li = -1;
	tree[t][ct[t]].ri = -1;
	tree[t][ct[t]].level = tree[t][idx].level + 1;
	tree[t][ct[t]].w = ll / (ll + lr) * tree[t][idx].w;
	tree[t][idx].li = ct[t];
	ct[t]++;
	tree[t][ct[t]].sp = points[t][maxp];
	tree[t][ct[t]].ep = tree[t][idx].ep;
	tree[t][ct[t]].si = maxp;
	tree[t][ct[t]].ei = tree[t][idx].ei;
	tree[t][ct[t]].li = -1;
	tree[t][ct[t]].ri = -1;
	tree[t][ct[t]].level = tree[t][idx].level + 1;
	tree[t][ct[t]].w = lr / (ll + lr) * tree[t][idx].w;
	tree[t][idx].ri = ct[t];
	ct[t]++;
}

struct Point calP(double len, struct Point left, struct Point right) {
	Point p;
	if (equal(left.x, right.x)) {
		p.x = left.x;
		p.y = left.y + len;
		return p;
	}
	if (equal(left.y, right.y)) {
		p.x = left.x + len;
		p.y = left.y;
		return p;
	}

	double k = (right.y - left.y) / (right.x - left.x);
	double b = left.y - k*left.x;
	double x0 = (right.x*left.y - left.x*right.y) / (left.y - right.y);
	double sinAlpha = sin(atan(k)), cosAlpha = cos(atan(k));
	if (DEBUG) printf("k=%lf sinAlpha=%lf left(%lf, %lf) right(%lf, %lf)\n", k, sinAlpha, left.x, left.y, right.x, right.y);

	p.y = left.y + fabs(len * sinAlpha) * (left.y < right.y? 1: -1);
	p.x = left.x + fabs(len * cosAlpha) * (left.x < right.x? 1: -1);

	return p;
}

double calR(int level, double len, struct Point left, struct Point right,
	struct Point *child1, struct Point *child2, double a1, double a2, double c1, double c2,
	double sinTheta1_1, double sinTheta1_2, double sinTheta2_1, double sinTheta2_2,
	double cosTheta1_1, double cosTheta1_2, double cosTheta2_1, double cosTheta2_2) {

	struct Point p1, p2;
	double R=0, d1=0, dd1=0, d2=0, dd2=0, r1=0, r2=0;

	if (child1 == NULL && child2 == NULL) {
		/* case 1 */
		dd1 = len / length(left, right);
		r1 = sqrt(1 - 2*dd1 + 2*dd1*dd1) * Cz;
		R += r1;
	} else {
		/* case 2 */
		if (child1 != NULL) {
			if (len / cosTheta1_1 < a1) {
				d1 = len / cosTheta1_1;
				dd1 = d1 / a1;
				R += d1 * sinTheta1_1;
				struct Point p = calP(d1, left, *child1);
				p1.x = p.x;
				p1.y = p.y;
			} else {
				d1 = (length(left, right)-len) / cosTheta1_2;
				dd1 = d1 / c1;
				R += d1 * sinTheta1_2;
				struct Point p = calP(c1 - d1, *child1, right);
				p1.x = p.x;
				p1.y = p.y;
			}
			r1 = sqrt(1 - 2*dd1 + 2*dd1*dd1) * Cz;
			R += r1;
		} else {
			struct Point p = calP(len, left, right);
			p1.x = p.x;
			p1.y = p.y;
		}
		if (child2 != NULL) {
			if (len / cosTheta2_1 < a2) {
				d2 = len / cosTheta2_1;
				dd2 = d2 / a2;
				R += d2 * sinTheta2_1;
				struct Point p = calP(d2, left, *child2);
				p2.x = p.x;
				p2.y = p.y;
			} else {
				d2 = (length(left, right)-len) / cosTheta2_2;
				dd2 = d2 / c2;
				R += d2 * sinTheta2_2;
				struct Point p = calP(c2 - d2, *child2, right);
				p2.x = p.x;
				p2.y = p.y;
			}
			r2 = sqrt(1 - 2*dd2 + 2*dd2*dd2) * Cz;
			// R += r2;
		} else {
			struct Point p = calP(len, left, right);
			p2.x = p.x;
			p2.y = p.y;
		}
	}
	if (DEBUG) {
		printf("R: length=%.6lf d1=%.6lf d2=%.6f r1=%.6lf r2=%.6f R=%.6lf\n", len, d1, d2, r1, r2, R);
		printf("p1(%lf, %lf) p2(%lf %lf)\n", p1.x, p1.y, p2.x, p2.y);
	}

	if (R > um[level]) {
		um[level] = R;
		ump[0][level] = p1;
		ump[1][level] = p2;
	}
	return R;
}

/* At least one angle is obtuse, i.e. child1 is not NULL */
double calR_obtuse(int level, double len, struct Point left, struct Point right,
	struct Point *child1, struct Point *child2, double a1, double a2, double b, double c1, double c2,
	double sinTheta1_1, double sinTheta1_2, double sinTheta2_1, double sinTheta2_2,
	double cosTheta1_1, double cosTheta1_2, double cosTheta2_1, double cosTheta2_2) {

	struct Point p1, p2, p;
	double R=0, d1=0, dd1=0, d2=0, dd2=0, r1=0, r2=0;
	double ratio = len / (a1 + c1);

	d1 = len;
	dd1 = (d1 < a1)? d1/a1: (d1-a1)/c1;
	if (child2 == NULL) {
		/* case 2.1 */
		d2 = ratio * b;
		if (d1 < a1)
			p = calP(d1, left, *child1);
		else
			p = calP(d1-a1, *child1, right);
		p1.x = p.x;
		p1.y = p.y;
		p = calP(d2, left, right);
		p2.x = p.x;
		p2.y = p.y;

		R += length(p1, p2);
	} else {
		/* case 2.2 */
		d2 = ratio * (a2 + c2);
		if (d1 < a1)
			p = calP(d1, left, *child1);
		else
			p = calP(d1-a1, *child1, right);
		p1.x = p.x;
		p1.y = p.y;
		if (d1 < a2)
			p = calP(d2, left, *child2);
		else
			p = calP(d2, *child2, right);
		p2.x = p.x;
		p2.y = p.y;

		R += length(p1, p2);
	}
	r1 = sqrt(1 - 2*dd1 + 2*dd1*dd1) * Cz;
	R += r1;

	if (DEBUG) {
		printf("R: length=%.6lf d1=%.6lf d2=%.6f r1=%.6lf r2=%.6f R=%.6lf\n", len, d1, d2, r1, r2, R);
		printf("p1(%lf, %lf) p2(%lf %lf)\n", p1.x, p1.y, p2.x, p2.y);
	}

	if (R > um[level]) {
		um[level] = R;
		ump[0][level] = p1;
		ump[1][level] = p2;
	}
	return R;
}

double calU(struct Point left, struct Point right, struct Point *child1, struct Point *child2, int level) {
	double b = length(left, right);
	double a1=0, a2=0, c1=0, c2=0;
	double cosTheta1_1=0, cosTheta1_2=0, cosTheta2_1=0, cosTheta2_2=0;
	double sinTheta1_1=0, sinTheta1_2=0, sinTheta2_1=0, sinTheta2_2=0;

	if (child1 != NULL) {
		a1 = length(left, *child1);
		c1 = length(*child1, right);
		cosTheta1_1 = cosine(a1, b, c1);
		cosTheta1_2 = cosine(c1, b, a1);
		sinTheta1_1 = sin(acos(cosTheta1_1));
		sinTheta1_2 = sin(acos(cosTheta1_2));
	}
	if (child2 != NULL) {
		a2 = length(left, *child2);
		c2 = length(*child2, right);
		cosTheta2_1 = cosine(a2, b, c2);
		cosTheta2_2 = cosine(c2, b, a2);
		sinTheta2_1 = sin(acos(cosTheta2_1));
		sinTheta2_2 = sin(acos(cosTheta2_2));
	}

	if (DEBUG) {
		printf("left(%.6lf %.6lf) right(%.6lf %.6lf) child1(%.6lf %.6lf) child2(%.6lf %.6lf)\n",
			left.x, left.y, right.x, right.y,
			(child1 != NULL)?child1->x:-1, (child1 != NULL)?child1->y:-1,
			(child2 != NULL)?child2->x:-1, (child2 != NULL)?child2->y:-1);
		printf("a1=%lf a2=%lf b=%lf c1=%lf c2=%lf cos1_1=%lf cos1_2=%lf cos2_1=%lf cos2_2=%lf sin1_1=%lf sin1_2=%lf sin2_1=%lf sin2_2=%lf\n",
			a1, a2, b, c1, c2, cosTheta1_1, cosTheta1_2, cosTheta2_1, cosTheta2_2, 
			sinTheta1_1, sinTheta1_2, sinTheta2_1, sinTheta2_2);
	}

	double sumR = 0;
	int count = 0;
	double len = 0;
	struct Point p;
	p.x = left.x;
	p.y = left.y;
	if (cosTheta1_1 < 0 || cosTheta1_2 < 0 || cosTheta2_1 < 0 || cosTheta2_2 < 0) {
		/* obtuse angle (child1 is not NULL) */
		double lenTotal = a1 + c1;
		while (len < lenTotal) {
			len += n;
			if (len < a1)
				p = calP(len, left, *child1);
			else
				p = calP(len-a1, *child1, right);
			sumR += calR_obtuse(level, len, left, right, child1, child2, a1, a2, b, c1, c2,
				sinTheta1_1, sinTheta1_2, sinTheta2_1, sinTheta2_2,
				cosTheta1_1, cosTheta1_2, cosTheta2_1, cosTheta2_2);
			count++;
		}
	} else {
		if (equal(left.x, right.x)) {
			/* perpendicular to x-axis */
			while (p.y < right.y) {
				len += n;
				p.y += n;
				sumR += calR(level, len, left, right, child1, child2, a1, a2, c1, c2,
					sinTheta1_1, sinTheta1_2, sinTheta2_1, sinTheta2_2,
					cosTheta1_1, cosTheta1_2, cosTheta2_1, cosTheta2_2);
				count++;
			}
		} else if (equal(left.y, right.y)) {
			/* perpendicular to y-axis */
			while (p.x < right.x) {
				len += n;
				p.x += n;
				sumR += calR(level, len, left, right, child1, child2, a1, a2, c1, c2,
					sinTheta1_1, sinTheta1_2, sinTheta2_1, sinTheta2_2,
					cosTheta1_1, cosTheta1_2, cosTheta2_1, cosTheta2_2);
				count++;
			}
		} else {
			while (p.x < right.x) {
				len += n;
				p = calP(len, left, right);

				sumR += calR(level, len, left, right, child1, child2, a1, a2, c1, c2,
					sinTheta1_1, sinTheta1_2, sinTheta2_1, sinTheta2_2,
					cosTheta1_1, cosTheta1_2, cosTheta2_1, cosTheta2_2);
				count++;
			}
		}
	}

	return sumR / count;
}

void qualityAssessment(struct Tree t1, struct Tree t2) {
	struct Point left  = equal(t1.sp.x, t1.ep.x)?
	((t1.sp.y < t1.ep.y)? t1.sp: t1.ep):
	((t1.sp.x < t1.ep.x)? t1.sp: t1.ep);
	struct Point right = equal(t1.sp.x, t1.ep.x)?
	((t1.sp.y < t1.ep.y)? t1.ep: t1.sp):
	((t1.sp.x < t1.ep.x)? t1.ep: t1.sp);

	if (t1.li == -1 && t2.li == -1) {
		/* case 1 */
		double U = calU(left, right, NULL, NULL, t1.level);
		u[t1.level] += U;
		uw += U * t1.w;
	} else if (t1.li != -1 && t2.li == -1) {
		/* case 2.1 with t1 */
		struct Point child = tree[0][t1.li].ep;
		double U = calU(left, right, &child, NULL, t1.level);
		u[t1.level] += U;
		uw += U * t1.w;
	} else if (t1.li == -1 && t2.li != -1) {
		/* case 2.1 with t2 */
		struct Point child = tree[1][t2.li].ep;
		double U = calU(left, right, &child, NULL, t1.level);
		u[t2.level] += U;
		uw += U * t2.w;
	} else {
		if (equal(tree[0][t1.li].sp, tree[1][t2.li].sp) && 
			equal(tree[0][t1.li].ep, tree[1][t2.li].ep) &&
			equal(tree[0][t1.ri].sp, tree[1][t2.ri].sp) &&
			equal(tree[0][t1.ri].ep, tree[1][t2.ri].ep)) 
		{
			qualityAssessment(tree[0][t1.li], tree[1][t2.li]);
			qualityAssessment(tree[0][t1.ri], tree[1][t2.ri]);
		} else {
			/* case 2.2 */
			struct Point child1 = tree[0][t1.li].ep;
			struct Point child2 = tree[1][t2.li].ep;
			double U = calU(left, right, &child1, &child2, t1.level);
			u[t1.level] += U;
			uw += U * t1.w;
		}
	}
}

int main(int argc, char **argv) {
	if (argc <= 4) {
		help();
		return 0;
	}
	FILE *fin[2] = { fopen(argv[1], "r"), fopen(argv[2], "r") };
	Cz = atof(argv[3]);
	n = atof(argv[4]);
	if (argc > 5) DEBUG = 1;

	for (int i=0; i<2; i++) {
		points[i] = (struct Point*) malloc(lp[i] * sizeof(struct Point));

		while (!feof(fin[i])) {
			if (fscanf(fin[i], "%lf%lf", &points[i][cp[i]].x, &points[i][cp[i]].y) == -1) break;
			cp[i]++;
			if (cp[i] >= lp[i]) {
				lp[i] *= 2;
				points[i] = (struct Point*) realloc(points[i], lp[i] * sizeof(struct Point));
			}
		}

		if (DEBUG) {
			for (int j=0; j<cp[i]; j++) {
				printf("%.6f %.6f\n", points[i][j].x, points[i][j].y);
			}
		}

		lt[i] = cp[i] * 2;
		tree[i] = (struct Tree*) malloc(lt[i] * sizeof(struct Tree));
		tree[i][0].sp = points[i][0];
		tree[i][0].ep = points[i][cp[i]-1];
		tree[i][0].si = 0;
		tree[i][0].ei = cp[i]-1;
		tree[i][0].li = -1;
		tree[i][0].ri = -1;
		tree[i][0].level = 0;
		tree[i][0].w = 1;
		ct[i]++;
		int h = 0;
		while (h < ct[i]) {
			split(i, h++);
		}

		printf("\n------------------------------ Tree %d ------------------------------\n", i);
		for (int j=0; j<ct[i]; j++) {
			printf("idx=%d sp(%.6lf %.6lf) ep(%.6lf %.6lf) si=%d ei=%d li=%d ri=%d level=%d w=%.6lf\n",
				j, tree[i][j].sp.x, tree[i][j].sp.y, tree[i][j].ep.x, tree[i][j].ep.y,
				tree[i][j].si, tree[i][j].ei, tree[i][j].li, tree[i][j].ri, tree[i][j].level, tree[i][j].w);
		}
	}

	int len = MAX(tree[0][ct[0]-1].level, tree[1][ct[1]-1].level) + 1;
	u = (double*) malloc(len * sizeof(double));
	um = (double*) malloc(len * sizeof(double));
	ump[0] = (struct Point*) malloc(len * sizeof(struct Point));
	ump[1] = (struct Point*) malloc(len * sizeof(struct Point));
	memset(u, 0, len * sizeof(double));
	memset(um, 0, len * sizeof(double));
	qualityAssessment(tree[0][0], tree[1][0]);

	printf("\n------------------------------ Output ------------------------------\n");
	for (int i=0; i<=tree[0][ct[0]-1].level; i++) {
		if (u[i] != 0) {
			printf("level=%d U=%.6lf Umax=%.6lf Umax at:\n", i, u[i], um[i]);
			printf("\tp1(%.6lf %.6lf) p2(%.6lf %.6lf)\n", ump[0][i].x, ump[0][i].y, ump[1][i].x, ump[1][i].y);
		}
	}
	printf("AU(Curve)=%.6f\n", uw);

	for (int i=0; i<2; i++) {
		free(points[i]);
		free(tree[i]);
	}
	return 0;
}