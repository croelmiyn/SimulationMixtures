
public class HydroCell3 {

    /*
    Simulation of hydrodynamic interactions following the algorithm of Hernandez-Ortiz et al. J. Chem. Phys. (2006)
    This class contains the codes for computing the source of flow terms
    Reminder: the flow is v_k(r_target) = sum_sources sum_q c_{k,i}(r_target,q,b) a_{i,j}(r_source,q,b) f_j
    with b = (z_target<z_source) the boolean indicating whether the target is below the source
    This computes
    a_{i,j}(r_s,q,b) = caij^0(b) [ (caij^1(b) z_s + caij^2(b)) e^qz_s + (caij^3(b) z_s + caij^4(b)) e^-qz_s ]
    and sum_q a_{i,j}(r_source,q,b) f_j
    and cumulates lambda = sum_sources sum_q a_{i,j}(r_source,q,b) f_j
     */

    // static variables

    static private double PI=Math.PI;

    static private double h; // half channel height

    static double A,L; // A=L^2, 2D area, L=W width of the simulation box

    static public int nk,nk2; // number of Fourier modes
    static private double qmax;

    static private double[][] c_a11,c_a12,c_a13,c_a14,c_a15,c_a16; // coefficients for aij
    static private double[][] c_a31,c_a32,c_a33,c_a34,c_a35,c_a36; // coefficients for aij

    static private double[] q,q2;

    static private double[] K, emK2a2, lij,mij;

    static double max;
    static double dx;


    // instantiable variables

    private double[] a11,a12,a13,a14,a15,a16, a31,a32,a33,a34,a35,a36;
    private double f01,f02,c0,c1_b,c1_a;

    private double[] af1_re,af2_re,af3_re,af4_re,af5_re,af6_re,af1_im,af2_im,af3_im,af4_im,af5_im,af6_im;

    private double x03;


    // static methods
    static void setConditions(double h0, double L0, double a, int n0){
        h = h0;
        L = L0;
        A = L*L;
        nk = n0;
        nk2=nk*nk;

        // precomputes wave numbers for c_aij coefficients computations
        q = new double[nk];
        q2 = new double[nk];
        K = new double[nk2];
        emK2a2 = new double[nk2];
        lij= new double[nk2];
        mij= new double[nk2];
        for(int i=0;i<nk;i++){
            q[i] = (2*i-(nk-1))*PI/L;  // symmetric qs, nk odd
            //q[i] = (2*i)*PI/L;
            q2[i] = q[i]*q[i];
        }
        qmax=(nk-1)*PI/L;
        for(int i=0;i<nk;i++){
            for(int j=0;j<nk;j++){
                K[i*nk+j] = sqrt(q[i]*q[i]+q[j]*q[j]);
                emK2a2[i*nk+j] = exp(-K[i*nk+j]*K[i*nk+j]*a*a);
                lij[i*nk+j] = q[i];
                mij[i*nk+j] = q[j];
            }
        }

        // precomputes the static c_aij coefficients
        setCoeffsA11();
        setCoeffsA12();
        setCoeffsA13();
        setCoeffsA14();
        setCoeffsA15();
        setCoeffsA16();

        setCoeffsA31();
        setCoeffsA32();
        setCoeffsA33();
        setCoeffsA34();
        setCoeffsA35();
        setCoeffsA36();

    }

    static private void setCoeffsA11(){

        c_a11 = new double[nk2][5];

        double k,l,m;
        double l2,m2,k2,e2hk,e4hk,e6hk,e8hk,e10hk;

        for (int i=0; i<nk; i++){// change the count m = 2pi/L*i
            for(int j =0; j<nk; j++){// change the count m = 2pi/L*j

                l = q[i];
                m = q[j];

                l2 = l*l;
                m2 = m*m;
                k2 = (l2+m2);
                k=sqrt(k2);

                if(k!=0) {
                    e2hk = exp(2 * h * k);
                    e4hk = e2hk*e2hk;
                    e6hk = e4hk*e2hk;
                    e8hk = e6hk*e2hk;
                    e10hk = e8hk*e2hk;

                    c_a11[i*nk+j][0] = 3 * PI * exp(k*h) / (k2 * k * A * (1 - e4hk) * (2 * e4hk * (1 + 8 * h * h * k2) - e4hk * e4hk - 1));

                    // e+kx3 term
                    // x3 term
                    c_a11[i*nk+j][1] = k*l2 + e8hk*(k*l2-4*k2*l2*h) + e4hk*(-2*l2*k+4*l2*k2*h) ;

                    // constant
                    c_a11[i*nk+j][2] = (h*k*l2+k2+m2) + e4hk*(2*k*l2*h-4*h*h*k2*(l2+8*m2)-2*(k2+m2));
                    c_a11[i*nk+j][2] += e8hk*(-3*l2*k*h+4*h*h*k2*l2+k2+m2) ;


                    // e-kx3 term
                    // x3 term
                    c_a11[i*nk+j][3] = e10hk*(k*l2) + e6hk*(-2*k*l2-4*k2*l2*h) + e2hk*(k*l2+4*l2*k2*h);

                    // constant
                    c_a11[i*nk+j][4] = e10hk * (h*k*l2-k2-m2) + e6hk * (2*k*l2*h+4*h*h*k2*(l2+8*m2)+2*(k2+m2));
                    c_a11[i*nk+j][4]+= e2hk * (-3*h*k*l2-4*h*h*k2*l2-k2-m2);

                }

            }
        }

    }

    static private void setCoeffsA12(){

        c_a12 = new double[nk2][5];

        double k,l,m;
        double l2,m2,k2,e2hk,e4hk,e6hk,e8hk,e10hk;

        for (int i=0; i<nk; i++){// change the count m = 2pi/L*i
            for(int j =0; j<nk; j++){// change the count m = 2pi/L*j

                l = q[i];
                m = q[j];

                l2 = l*l;
                m2 = m*m;
                k2 = (l2+m2);
                k=sqrt(k2);

                if(k!=0) {

                    e2hk = exp(2 * h * k);
                    e4hk = e2hk*e2hk;
                    e6hk = e4hk*e2hk;
                    e8hk = e6hk*e2hk;
                    e10hk = e8hk*e2hk;

                    c_a12[i*nk+j][0] = 3 * PI *m*l* exp(h*k)/ (k2 * k * A * (e4hk-1) * (2 * e4hk * (1 + 8 * h * h * k2) - e8hk  - 1));

                    // e+kx3 term
                    // x3 term
                    c_a12[i*nk+j][1] = -k +  e8hk*(-k+4*h*k2) + e4hk*(2*k-4*h*k2);

                    // constant
                    c_a12[i*nk+j][2] = (-k*h+1) +  e8hk*(3*h*k-4*h*h*k2+1) +  e4hk*(-2*k*h-28*h*h*k2-2) ;


                    // e-kx3 term
                    // x3 term
                    c_a12[i*nk+j][3] =  e10hk*(-k) + e2hk*(-k-4*h*k2) + e6hk*(2*k+4*h*k2);

                    // constant
                    c_a12[i*nk+j][4] =  e10hk*(-1-h*k) + e2hk*(3*h*k+4*h*h*k2-1) + e6hk*(-2*h*k+28*h*h*k2+2);

                }

            }
        }

    }

    static private void setCoeffsA13(){ //!!!!!!!! a13 is imaginary !!!!!! this is to compute the imaginary part

        c_a13 = new double[nk2][5];

        double k,l,m;
        double l2,m2,k2,e2hk,e4hk,e6hk,e8hk,e10hk;

        for (int i=0; i<nk; i++){// change the count m = 2pi/L*i
            for(int j =0; j<nk; j++){// change the count m = 2pi/L*j

                l = q[i];
                m = q[j];

                l2 = l*l;
                m2 = m*m;
                k2 = (l2+m2);
                k=sqrt(k2);

                if(k!=0) {
                    e2hk = exp(2 * h * k);
                    e4hk = e2hk*e2hk;
                    e6hk = e4hk*e2hk;
                    e8hk = e6hk*e2hk;

                    c_a13[i*nk+j][0] = 3 * PI *l* exp(h*k)/ ( k * A  * (2 * e4hk * (1 + 8 * h * h * k2) - e8hk  - 1));

                    // e+kx3 term
                    // x3 term
                    c_a13[i*nk+j][1] = 1+ e4hk * (-1-4*h*k);

                    // constant
                    c_a13[i*nk+j][2] = h+ e4hk * (-h+4*h*h*k);


                    // e-kx3 term
                    // x3 term
                    c_a13[i*nk+j][3] = e6hk * (1) + e2hk * (-1+4*k*h);

                    // constant
                    c_a13[i*nk+j][4] = e6hk * (h) + e2hk * (-h-4*h*h*k);

                }

            }
        }

    }

    static private void setCoeffsA14(){

        c_a14 = new double[nk2][5];

        double k,l,m;
        double l2,m2,k2,e2hk,e4hk,e6hk,e8hk,e10hk,e12hk;

        for (int i=0; i<nk; i++){// change the count m = 2pi/L*i
            for(int j =0; j<nk; j++){// change the count m = 2pi/L*j

                l = q[i];
                m = q[j];

                l2 = l*l;
                m2 = m*m;
                k2 = (l2+m2);
                k=sqrt(k2);

                if(k!=0) {
                    e2hk = exp(2 * h * k);
                    e4hk = e2hk*e2hk;
                    e6hk = e4hk*e2hk;
                    e8hk = e6hk*e2hk;
                    e10hk = e8hk*e2hk;
                    e12hk = e10hk*e2hk;

                    c_a14[i*nk+j][0] = 3 * PI * exp(-h*k)/ (k2 * k * A * (1 - e4hk) * (2 * e4hk * (1 + 8 * h * h * k2) - e8hk  - 1));

                    // e+kx3 term
                    // x3 term
                    //c_a14[i][j][1] = -k*l2*e12hk + e8hk*(2*k*l2+4*k2*l2*h) + e4hk*(-l2*k+4*m2*k2*h) ;
                    c_a14[i*nk+j][1] = -k*l2*e12hk + e8hk*(2*k*l2+4*k2*l2*h) + e4hk*(-l2*k-4*l2*k2*h) ; // correction according to symmetry

                    // constant
                    c_a14[i*nk+j][2] = (h*k*l2-k2-m2)*e12hk + e8hk*(2*k*l2*h+4*h*h*k2*(l2+8*m2)+2*(k2+m2));
                    c_a14[i*nk+j][2] += e4hk*(-3*l2*k*h-4*h*h*k2*l2-k2-m2) ;


                    // e-kx3 term
                    // x3 term
                    //c_a14[i][j][3] = e2hk*(-k*l2) + e6hk*(2*k*l2-4*k2*l2*h) + e10hk*(-k*l2-4*m2*k2*h);
                    c_a14[i*nk+j][3] = e2hk*(-k*l2) + e6hk*(2*k*l2-4*k2*l2*h) + e10hk*(-k*l2+4*l2*k2*h); // correction according to symetry


                    // constant
                    c_a14[i*nk+j][4] = e2hk * (h*k*l2+k2+m2) + e6hk * (2*k*l2*h-4*h*h*k2*(l2+8*m2)-2*(k2+m2));
                    c_a14[i*nk+j][4]+= e10hk * (-3*h*k*l2+4*h*h*k2*l2+k2+m2);


                }

            }
        }

    }

    static private void setCoeffsA15(){

        c_a15 = new double[nk2][5];

        double k,l,m;
        double l2,m2,k2,e2hk,e4hk,e6hk,e8hk,e10hk,e12hk;

        for (int i=0; i<nk; i++){// change the count m = 2pi/L*i
            for(int j =0; j<nk; j++){// change the count m = 2pi/L*j

                l = q[i];
                m = q[j];

                l2 = l*l;
                m2 = m*m;
                k2 = (l2+m2);
                k=sqrt(k2);

                if(k!=0) {
                    e2hk = exp(2 * h * k);
                    e4hk = e2hk*e2hk;
                    e6hk = e4hk*e2hk;
                    e8hk = e6hk*e2hk;
                    e10hk = e8hk*e2hk;
                    e12hk = e10hk*e2hk;

                    c_a15[i*nk+j][0] = 3 * PI *m*l* exp(-h*k)/ (k2 * k * A * (e4hk-1) * (2 * e4hk * (1 + 8 * h * h * k2) - e8hk  - 1));

                    // e+kx3 term
                    // x3 term
                    c_a15[i*nk+j][1] = e12hk*k +  e4hk*(k+4*h*k2) + e8hk*(-2*k-4*h*k2);

                    // constant
                    c_a15[i*nk+j][2] = -e12hk*(k*h+1) +  e4hk*(3*h*k+4*h*h*k2-1) +  e8hk*(-2*k*h+28*h*h*k2+2) ;


                    // e-kx3 term
                    // x3 term
                    c_a15[i*nk+j][3] =  e2hk*k + e10hk*(k-4*h*k2) + e6hk*(-2*k+4*h*k2);

                    // constant
                    c_a15[i*nk+j][4] =  e2hk*(1-h*k) + e10hk*(3*h*k-4*h*h*k2+1) + e6hk*(-2*h*k-28*h*h*k2-2);


                }

            }
        }

    }

    static private void setCoeffsA16(){  // is imaginary !!!!  THIS IS IMAGIMARY PART !!!!!

        c_a16 = new double[nk2][5];

        double k,l,m;
        double l2,m2,k2,e2hk,e4hk,e6hk,e8hk,e10hk,e12hk;

        for (int i=0; i<nk; i++){// change the count m = 2pi/L*i
            for(int j =0; j<nk; j++){// change the count m = 2pi/L*j

                l = q[i];
                m = q[j];

                l2 = l*l;
                m2 = m*m;
                k2 = (l2+m2);
                k=sqrt(k2);

                if(k!=0) {
                    e2hk = exp(2 * h * k);
                    e4hk = e2hk*e2hk;
                    e6hk = e4hk*e2hk;
                    e8hk = e6hk*e2hk;

                    c_a16[i*nk+j][0] = -3 * PI *l* exp(-h*k)/ ( k * A  * (2 * e4hk * (1 + 8 * h * h * k2) - e8hk  - 1));

                    // e+kx3 term
                    // x3 term
                    c_a16[i*nk+j][1] = e8hk * (-1) + e4hk * (1-4*h*k);

                    // constant
                    c_a16[i*nk+j][2] = e8hk * h + e4hk * (-h-4*h*h*k);


                    // e-kx3 term
                    // x3 term
                    c_a16[i*nk+j][3] = e2hk * (-1) + e6hk * (1+4*k*h);

                    // constant
                    c_a16[i*nk+j][4] = e2hk * (h) + e6hk * (-h+4*h*h*k);


                }

            }
        }

    }

    static private void setCoeffsA31(){ //!!!!!!!! a31 is imaginary !!!!!! this is to compute the imaginary part

        c_a31 = new double[nk2][5];

        double k,l,m;
        double l2,m2,k2,e2hk,e4hk,e6hk,e8hk,e10hk;

        for (int i=0; i<nk; i++){// change the count m = 2pi/L*i
            for(int j =0; j<nk; j++){// change the count m = 2pi/L*j

                l = q[i];
                m = q[j];

                l2 = l*l;
                m2 = m*m;
                k2 = (l2+m2);
                k=sqrt(k2);

                if(k!=0) {
                    e2hk = exp(2 * h * k);
                    e4hk = e2hk*e2hk;
                    e6hk = e4hk*e2hk;
                    e8hk = e6hk*e2hk;
                    e10hk = e8hk*e2hk;

                    c_a31[i*nk+j][0] = 3 * PI *l* exp(-3*h*k)/ ( k * A  * (2 * e4hk * (1 + 8 * h * h * k2) - e8hk  - 1));

                    // e+kx3 term
                    // x3 term
                    c_a31[i*nk+j][1] = e8hk * (-1+4*h*k) + e4hk;

                    // constant
                    c_a31[i*nk+j][2] = e8hk * (-h-4*h*h*k) + e4hk * h;


                    // e-kx3 term
                    // x3 term
                    c_a31[i*nk+j][3] = e10hk * (1) + e6hk * (-1-4*k*h);

                    // constant
                    c_a31[i*nk+j][4] = e10hk * (h) + e6hk * (-h+4*h*h*k);

                }

            }
        }

    }

    static private void setCoeffsA32(){ //!!!!!!!! a32 is imaginary !!!!!! this is to compute the imaginary part

        c_a32 = new double[nk2][5];

        double k,l,m;
        double l2,m2,k2,e2hk,e4hk,e6hk,e8hk,e10hk;

        for (int i=0; i<nk; i++){// change the count m = 2pi/L*i
            for(int j =0; j<nk; j++){// change the count m = 2pi/L*j

                l = q[i];
                m = q[j];

                l2 = l*l;
                m2 = m*m;
                k2 = (l2+m2);
                k=sqrt(k2);

                if(k!=0) {
                    e2hk = exp(2 * h * k);
                    e4hk = e2hk*e2hk;
                    e6hk = e4hk*e2hk;
                    e8hk = e6hk*e2hk;
                    e10hk = e8hk*e2hk;

                    c_a32[i*nk+j][0] = 3 * PI *m* exp(-3*h*k)/ ( k * A  * (2 * e4hk * (1 + 8 * h * h * k2) - e8hk  - 1));

                    // e+kx3 term
                    // x3 term
                    c_a32[i*nk+j][1] = e8hk * (-1+4*h*k) + e4hk;

                    // constant
                    c_a32[i*nk+j][2] = e8hk * (-h-4*h*h*k) + e4hk * h;


                    // e-kx3 term
                    // x3 term
                    c_a32[i*nk+j][3] = e10hk * (1) + e6hk * (-1-4*k*h);

                    // constant
                    c_a32[i*nk+j][4] = e10hk * (h) + e6hk * (-h+4*h*h*k);

                }

            }
        }

    }

    static private void setCoeffsA33(){ //!!!!!!!! a33 is real !!!!!!

        c_a33 = new double[nk2][5];

        double k,l,m;
        double l2,m2,k2,e2hk,e4hk,e6hk,e8hk,e10hk;

        for (int i=0; i<nk; i++){// change the count m = 2pi/L*i
            for(int j =0; j<nk; j++){// change the count m = 2pi/L*j

                l = q[i];
                m = q[j];

                l2 = l*l;
                m2 = m*m;
                k2 = (l2+m2);
                k=sqrt(k2);

                if(k!=0) {
                    e2hk = exp(2 * h * k);
                    e4hk = e2hk*e2hk;
                    e6hk = e4hk*e2hk;
                    e8hk = e6hk*e2hk;
                    e10hk = e8hk*e2hk;

                    c_a33[i*nk+j][0] = 3 * PI * exp(-3*h*k)/ ( k * A  * (2 * e4hk * (1 + 8 * h * h * k2) - e8hk  - 1));

                    // e+kx3 term
                    // x3 term
                    c_a33[i*nk+j][1] = e8hk * (k+4*h*k2) + e4hk *(-k);

                    // constant
                    c_a33[i*nk+j][2] = e8hk * (-3*h*k-4*h*h*k2-1) + e4hk * (1-k*h);


                    // e-kx3 term
                    // x3 term
                    c_a33[i*nk+j][3] = e10hk * (k) + e6hk * (-k+4*k2*h);

                    // constant
                    c_a33[i*nk+j][4] = e10hk * (h*k+1) + e6hk * (3*h*k-4*h*h*k2-1);

                }

            }
        }

    }

    static private void setCoeffsA34(){ //!!!!!!!! a34 is imaginary !!!!!! this is to compute the imaginary part

        c_a34 = new double[nk2][5];

        double k,l,m;
        double l2,m2,k2,e2hk,e4hk,e6hk,e8hk;

        for (int i=0; i<nk; i++){// change the count m = 2pi/L*i
            for(int j =0; j<nk; j++){// change the count m = 2pi/L*j

                l = q[i];
                m = q[j];

                l2 = l*l;
                m2 = m*m;
                k2 = (l2+m2);
                k=sqrt(k2);

                if(k!=0) {
                    e2hk = exp(2 * h * k);
                    e4hk = e2hk*e2hk;
                    e6hk = e4hk*e2hk;
                    e8hk = e6hk*e2hk;

                    c_a34[i*nk+j][0] = -3 * PI *l* exp(-h*k)/ ( k * A  * (2 * e4hk * (1 + 8 * h * h * k2) - e8hk  - 1));

                    // e+kx3 term
                    // x3 term
                    c_a34[i*nk+j][1] = e4hk * (1+4*h*k) - e8hk;

                    // constant
                    c_a34[i*nk+j][2] = e4hk * (-h+4*h*h*k) + e8hk * h;


                    // e-kx3 term
                    // x3 term
                    c_a34[i*nk+j][3] = e2hk * (-1) + e6hk * (1-4*k*h);

                    // constant
                    c_a34[i*nk+j][4] = e2hk * (h) + e6hk * (-h-4*h*h*k);

                }

            }
        }

    }

    static private void setCoeffsA35(){ //!!!!!!!! a35 is imaginary !!!!!! this is to compute the imaginary part

        c_a35 = new double[nk2][5];

        double k,l,m;
        double l2,m2,k2,e2hk,e4hk,e6hk,e8hk;

        for (int i=0; i<nk; i++){// change the count m = 2pi/L*i
            for(int j =0; j<nk; j++){// change the count m = 2pi/L*j

                l = q[i];
                m = q[j];

                l2 = l*l;
                m2 = m*m;
                k2 = (l2+m2);
                k=sqrt(k2);

                if(k!=0) {
                    e2hk = exp(2 * h * k);
                    e4hk = e2hk*e2hk;
                    e6hk = e4hk*e2hk;
                    e8hk = e6hk*e2hk;

                    c_a35[i*nk+j][0] = -3 * PI *m* exp(-h*k)/ ( k * A  * (2 * e4hk * (1 + 8 * h * h * k2) - e8hk  - 1));

                    // e+kx3 term
                    // x3 term
                    c_a35[i*nk+j][1] = e4hk * (1+4*h*k) - e8hk;

                    // constant
                    c_a35[i*nk+j][2] = e4hk * (-h+4*h*h*k) + e8hk * h;


                    // e-kx3 term
                    // x3 term
                    c_a35[i*nk+j][3] = e2hk * (-1) + e6hk * (1-4*k*h);

                    // constant
                    c_a35[i*nk+j][4] = e2hk * (h) + e6hk * (-h-4*h*h*k);

                }

            }
        }

    }

    static private void setCoeffsA36(){ //!!!!!!!! a33 is real !!!!!!

        c_a36 = new double[nk2][5];

        double k,l,m;
        double l2,m2,k2,e2hk,e4hk,e6hk,e8hk,e10hk;

        for (int i=0; i<nk; i++){// change the count m = 2pi/L*i
            for(int j =0; j<nk; j++){// change the count m = 2pi/L*j

                l = q[i];
                m = q[j];

                l2 = l*l;
                m2 = m*m;
                k2 = (l2+m2);
                k=sqrt(k2);

                if(k!=0) {
                    e2hk = exp(2 * h * k);
                    e4hk = e2hk*e2hk;
                    e6hk = e4hk*e2hk;
                    e8hk = e6hk*e2hk;

                    c_a36[i*nk+j][0] = -3 * PI * exp(-h*k)/ ( k * A  * (2 * e4hk * (1 + 8 * h * h * k2) - e8hk  - 1));

                    // e+kx3 term
                    // x3 term
                    c_a36[i*nk+j][1] = e4hk * (-k+4*h*k2) + e8hk *(k);

                    // constant
                    c_a36[i*nk+j][2] = e4hk * (-3*h*k+4*h*h*k2+1) + e8hk * (-1-k*h);


                    // e-kx3 term
                    // x3 term
                    c_a36[i*nk+j][3] = e2hk * (-k) + e6hk * (k+4*k2*h);

                    // constant
                    c_a36[i*nk+j][4] = e2hk * (h*k-1) + e6hk * (3*h*k+4*h*h*k2+1);

                }

            }
        }

    }

    static private double exp(double x){
        return Math.exp(x);
    }
    static private double sqrt(double x){
        return Math.sqrt(x);
    }


    // instance methods

    // constructor
    HydroCell3(){
        setFourierModes();
    }

    public void setFourierModes(){

        a11 = new double[nk2];
        a12 = new double[nk2];
        a13 = new double[nk2];
        a14 = new double[nk2];
        a15 = new double[nk2];
        a16 = new double[nk2];

        a31 = new double[nk2];
        a32 = new double[nk2];
        a33 = new double[nk2];
        a34 = new double[nk2];
        a35 = new double[nk2];
        a36 = new double[nk2];
    }

    // for computing the aij coefficients of the point source
    private void computeCoeffs(double x3){
        CalcA1s(x3);
        CalcA3s(x3);
    }

    private void CalcA1s(double x3){

        double ekx;
        double[] c1lm,c2lm,c3lm,c4lm,c5lm,c6lm;

        for (int lm=0; lm<nk2; lm++){
            c1lm = c_a11[lm];
            c2lm = c_a12[lm];
            c3lm = c_a13[lm];
            c4lm = c_a14[lm];
            c5lm = c_a15[lm];
            c6lm = c_a16[lm];
                
            ekx = exp(K[lm]*x3);

            a11[lm] = c1lm[0] * ( (c1lm[1]*x3 + c1lm[2]) * ekx + (c1lm[3]*x3 + c1lm[4]) / ekx );
            a12[lm] = c2lm[0] * ( (c2lm[1]*x3 + c2lm[2]) * ekx + (c2lm[3]*x3 + c2lm[4]) / ekx );
            a13[lm] = c3lm[0] * ( (c3lm[1]*x3 + c3lm[2]) * ekx + (c3lm[3]*x3 + c3lm[4]) / ekx );
            a14[lm] = c4lm[0] * ( (c4lm[1]*x3 + c4lm[2]) * ekx + (c4lm[3]*x3 + c4lm[4]) / ekx );
            a15[lm] = c5lm[0] * ( (c5lm[1]*x3 + c5lm[2]) * ekx + (c5lm[3]*x3 + c5lm[4]) / ekx );
            a16[lm] = c6lm[0] * ( (c6lm[1]*x3 + c6lm[2]) * ekx + (c6lm[3]*x3 + c6lm[4]) / ekx );

        }

    }

    private void CalcA3s(double x3){

        double ekx;
        double[] c1lm,c2lm,c3lm,c4lm,c5lm,c6lm;

        for (int lm=0; lm<nk2; lm++){
            c1lm = c_a31[lm];
            c2lm = c_a32[lm];
            c3lm = c_a33[lm];
            c4lm = c_a34[lm];
            c5lm = c_a35[lm];
            c6lm = c_a36[lm];

            ekx = exp(K[lm]*x3);

            a31[lm] = c1lm[0] * ( (c1lm[1]*x3 + c1lm[2]) * ekx + (c1lm[3]*x3 + c1lm[4]) / ekx );
            a32[lm] = c2lm[0] * ( (c2lm[1]*x3 + c2lm[2]) * ekx + (c2lm[3]*x3 + c2lm[4]) / ekx );
            a33[lm] = c3lm[0] * ( (c3lm[1]*x3 + c3lm[2]) * ekx + (c3lm[3]*x3 + c3lm[4]) / ekx );


            a34[lm] = c4lm[0] * ( (c4lm[1]*x3 + c4lm[2]) * ekx + (c4lm[3]*x3 + c4lm[4]) / ekx );  // assuming sign error
            a35[lm] = c5lm[0] * ( (c5lm[1]*x3 + c5lm[2]) * ekx + (c5lm[3]*x3 + c5lm[4]) / ekx );
            a36[lm] = c6lm[0] * ( (c6lm[1]*x3 + c6lm[2]) * ekx + (c6lm[3]*x3 + c6lm[4]) / ekx );

        }

    }

    // computes the aij.fj term, i.e. the contribution of the source to the flow
    public void calcAfs(double x1,double x2, double x3, double f1, double f2, double f3) {

        x03 = x3;

        computeCoeffs(x3);

        af1_re = new double[nk2];
        af2_re = new double[nk2];
        af3_re = new double[nk2];
        af4_re = new double[nk2];
        af5_re = new double[nk2];
        af6_re = new double[nk2];

        af1_im = new double[nk2];
        af2_im = new double[nk2];
        af3_im = new double[nk2];
        af4_im = new double[nk2];
        af5_im = new double[nk2];
        af6_im = new double[nk2];

        // coeffs for k=0
        f01 = f1;
        f02 = f2;
        c0 = -9*PI*(h*h-x3*x3)/(4*A*h*h*h);
        c1_b = -6*PI*(x3-h)/(2*A*h);
        c1_a = -6*PI*(x3+h)/(2*A*h);

        double l, m,emKa2ij, coskx, sinkx;
        int ij,in,ji;

        for (int i = 0; i < nk; i++) {// change the count l = 2pi/L*i
            l = q[i]*x1;
            in = i*nk;
            for (int j = 0; j < nk; j++) {// change the count m = 2pi/L*j
                m = l+q[j]*x2;
                emKa2ij = emK2a2[i*nk+j]; // coeffs = 0 for K=0
                ij = in+j;
                ji = j*nk+i;
                coskx = Math.cos(m);
                sinkx = Math.sin(m);

                af1_re[ij] = emKa2ij * ( (a11[ij] * f1 + a12[ji] * f2) * coskx + (a31[ij] * f3) * sinkx);
                af1_im[ij] = emKa2ij * (-(a11[ij] * f1 + a12[ji] * f2) * sinkx + (a31[ij] * f3) * coskx);

                af2_re[ij] = emKa2ij * ( (a12[ij] * f1 + a11[ji] * f2) * coskx + (a32[ij] * f3) * sinkx);
                af2_im[ij] = emKa2ij * (-(a12[ij] * f1 + a11[ji] * f2) * sinkx + (a32[ij] * f3) * coskx);

                af3_re[ij] = emKa2ij * ( (a33[ij] * f3) * coskx + (a13[ij] * f1 + a13[ji] * f2) * sinkx);
                af3_im[ij] = emKa2ij * (-(a33[ij] * f3) * sinkx + (a13[ij] * f1 + a13[ji] * f2) * coskx);

                // bottom
                af4_re[ij] = emKa2ij * ( (a14[ij] * f1 + a15[ji] * f2) * coskx + (a34[ij] * f3) * sinkx);
                af4_im[ij] = emKa2ij * (-(a14[ij] * f1 + a15[ji] * f2) * sinkx + (a34[ij] * f3) * coskx);

                af5_re[ij] = emKa2ij * ( (a15[ij] * f1 + a14[ji] * f2) * coskx + (a35[ij] * f3) * sinkx);
                af5_im[ij] = emKa2ij * (-(a15[ij] * f1 + a14[ji] * f2) * sinkx + (a35[ij] * f3) * coskx);

                af6_re[ij] = emKa2ij * ( (a36[ij] * f3) * coskx + (a16[ij] * f1 + a16[ji] * f2) * sinkx);
                af6_im[ij] = emKa2ij * (-(a36[ij] * f3) * sinkx + (a16[ij] * f1 + a16[ji] * f2) * coskx);

            }
        }



    }

    // to compute the velocity generated by this source in the target point stored in nM
    public double[] getVelocity(HydroTargetCoeffs2 nM){

        boolean b = nM.getRelativePosition(x03); // b=true <-> target below source

        double[] v = new double[3];

        double[] coskx = nM.getCos();
        double[] sinkx = nM.getSin();
        double[] C_l2  = nM.getC_l2(b);
        double[] C_m2  = nM.getC_m2(b);
        double[] C_k2  = nM.getC_k2(b);
        double[] C_l   = nM.getC_l(b);
        double[] C_m   = nM.getC_m(b);
        double[] C_lm  = nM.getC_lm(b);

        double cf;

        double[] aF1_re = (b)?af1_re:af4_re;
        double[] aF1_im = (b)?af1_im:af4_im;

        double[] aF2_re = (b)?af2_re:af5_re;
        double[] aF2_im = (b)?af2_im:af5_im;

        double[] aF3_re = (b)?af3_re:af6_re;
        double[] aF3_im = (b)?af3_im:af6_im;


        for (int ij = 0; ij < nk2; ij++) {// change the count l = 2pi/L*i

            // real part of v = Re1*Re2-Im1*Im2
                v[0] += coskx[ij] * ( C_l2[ij] * aF1_re[ij] + C_lm[ij] * aF2_re[ij] + C_l[ij] * aF3_im[ij]) //  Re1*Re2
                      + sinkx[ij] * (-C_l2[ij] * aF1_im[ij] - C_lm[ij] * aF2_im[ij] + C_l[ij] * aF3_re[ij]); // -Im1*Im2

                v[1] += coskx[ij] * ( C_lm[ij] * aF1_re[ij] + C_m2[ij] * aF2_re[ij] + C_m[ij] * aF3_im[ij]) //  Re*Re
                      + sinkx[ij] * (-C_lm[ij] * aF1_im[ij] - C_m2[ij] * aF2_im[ij] + C_m[ij] * aF3_re[ij]); // -Im*Im

                v[2] += coskx[ij] * (C_l[ij] * aF1_im[ij] + C_m[ij] * aF2_im[ij] + C_k2[ij] * aF3_re[ij]) //  Re*Re
                      + sinkx[ij] * (C_l[ij] * aF1_re[ij] + C_m[ij] * aF2_re[ij] - C_k2[ij] * aF3_im[ij]); // -Im*Im

        }
        // q=0 Fourier mode
        cf = (c0*nM.getCk01() + ((b)?c1_b:c1_a) * nM.getCk02(b));
        v[0] += f01*cf;
        v[1] += f02*cf;

        return v;

    }

    // adds the aij.fj term to the global source term lambda
    public void addAF(double[][] lambda, double cF[], boolean  b){  // b=true <-> target below source
        double[] aF1_re = (b)?af1_re:af4_re;
        double[] aF1_im = (b)?af1_im:af4_im;

        double[] aF2_re = (b)?af2_re:af5_re;
        double[] aF2_im = (b)?af2_im:af5_im;

        double[] aF3_re = (b)?af3_re:af6_re;
        double[] aF3_im = (b)?af3_im:af6_im;

        //* coefficients of q=/=0 Fourier modes
        for (int ij = 0; ij < nk2; ij++) {

            lambda[0][ij] += aF1_re[ij];
            lambda[1][ij] += aF2_re[ij];
            lambda[2][ij] += aF3_re[ij];

            lambda[3][ij] += aF1_im[ij];
            lambda[4][ij] += aF2_im[ij];
            lambda[5][ij] += aF3_im[ij];
        }
        //*/

        // coefficients of q=0 Fourier mode
        cF[0] += c0*f01;
        cF[1] +=((b)?c1_b:c1_a)*f01;
        cF[2] += c0*f02;
        cF[3] +=((b)?c1_b:c1_a)*f02;

    }


}
