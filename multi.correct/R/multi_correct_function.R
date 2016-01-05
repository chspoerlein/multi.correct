#' Multilevel Models to Calculate Index of Dissimilarity
#'
#'This package calculates the Index of Dissimilarity (from hereon denoted as D) using multilevel 
#'logistic regression. Lower level units are nested within the units for which segregation is to be 
#'calculated (e.g., immigrants and natives nested in neighborhoods). The random effects of the 
#'multilevel models serve as "naive" estimator of segregation conceptually and are used to simulated new marginal distributions for each group. The advantage 
#'of using this methods lies in the researchers ability to correct the D for compositional 
#'differences across the two groups by adding corresponding variables as well as correcting for 
#'contextual differences. The function allows the calculation of D via two and three level models.
#' @param group Indicator variable denoting the groups (e.g., 0=male, 1=female or 0=native, 1=immigrant).
#' @param district1 Units of segregation, denotes the variable that records units of segregation (i.e., districts).
#' @param district2 Units of segregation in three level model. Defaults to 1 denoting the estimation of a two-level model.
#' @param comp Compositional characteristics, list of variables for which D is to be correct for (e.g., age+sex+education). Defaults to 1 denoting that the uncorrected version of D is calculated.
#' @param data Name of dataset.
#' @param nsim Number of simulations. Defaults to 1000.
#' @param seed Seed number. Defaults to 12345.
#' @keywords multilevel
#' @keywords index of dissimilarity
#' @keywords compositional differences
#' @export
#' 
#' @examples 
#' ## Index of Dissimilarity for immigrants and natives over city districts: 
#' D <- multi_correct(group="immigrants", district1="citydistr", district2=1, comp=1, data=cityofX)
#' summary(D$Dm1)
#' 
#' ## Correcting D for compositional differences
#' D2 <- multi_correct(group="immigrants", district1="citydistr", district2=1, comp="age+sex+edu+income", data=cityofX)
#' summary(D2$Dm1)
#' 
#' ## D for segregation over cities and their districts
#' ## IMPORTANT: district1 needs to contain unit-ID with the fewest number of units
#' ## we have fewer cities than city districts in the data, therefore city is district1.
#' D3 <- multi_correct(group="immigrants", district1="city", district2="citydistr", comp="age+sex+edu+income", data=cityofX)
#' 
#' ## city segregation
#' summary(D3$Dm1)
#' 
#' ## city district segregation
#' summary(D3$Dm2)
#' 
#' @import lme4
#' @import boot
#' @author Christoph Spörlein, \email{christoph.spoerlein@@uni-bamberg.de}
#' @references Leckie et al. 2012: Multilevel Modeling of Social Segregation. Journal of Educational and Behavioral Statistics 37:3-29


multi_correct <- function(group, district1, district2=1, comp=1, data, nsim=1000, seed=12345){
  # setting seed for random number generator
  set.seed(seed)


######################################################################################################################## 
## THE FOLLOWING CODE IS ONLY USED IN 2-LEVEL MODELS ###################################################################
########################################################################################################################

  # check whether 2 or 3 level model specified
  if (district2==1) {

  # keep relevant data
  form1 <- paste0(group,"~",comp,"+",district1)
  mod <- lm(form1, data=data)
  datanomiss <- mod$model

  # summarize data for further use
  data2 <- table(datanomiss[,district1],datanomiss[,group])
  
  # implement stopping condition in case indicator variable has more than 2 categories
  if (ncol(data2)>2) {
    stop("grouping variable has more than two values")
  }
  
  # number of macro units
  nuj <- nrow(data2)
  
  # constructing model
  form <- paste0(group,"~",comp,"+(1|",district1,")") 
  
  # null model for scale correction
  form0 <- paste0(group," ~ 1+(1|",district1,")")
  model0 <- glmer(formula=form0, data=datanomiss, family = binomial(link="logit"), nAGQ=0)  
  
  
  # model
  model <- glmer(formula=form, data=datanomiss, family = binomial(link="logit"), nAGQ=0)
  
  ##############################################################################################################
  ################### extract information necessary to compute scale correction factor #########################
  ##############################################################################################################  
  
  # total variance null model
  u0_j <- as.data.frame(VarCorr(model0))
  total_var <- 3.29+((u0_j$sdcor)^2)
  total_var2 <- sqrt(total_var)
  
  # variance linear predictor
  var_lin <- var(predict(model, re.form=NA))
  
  # scale reduction factor
  srf <- total_var2/sqrt((var_lin+total_var))
  srf <- srf*srf

  ##############################################################################################################
  ################### begin simulating the random effects ######################################################
  ##############################################################################################################  
  
  # saving random effect
  u_j <- as.data.frame(VarCorr(model))
  u_j <- (u_j$sdcor)^2
  
  # apply scale reduction factor
  u_j_srf <- u_j*srf

  # calculate R2 2nd level
  r2_1 <- (((u0_j$sdcor)^2)-(u_j_srf))/((u0_j$sdcor)^2)
  
  # saving intercept
  b0 <- as.numeric(fixef(model)[1])
  
  # apply scale reduction factor
  b0_srf <- b0*srf
  
  u_j_srf <- sqrt(u_j_srf)  

  # preparing empty vectors to be filled in the simulation  
  usim_j <- matrix(rep(0, nsim*nuj), nrow=nuj)
  psim <- matrix(rep(0, nsim*nuj), nrow=nuj)
  
  # simulating begins here
  for (i in 1:nsim) {
    for (j in 1:nuj) {
      usim_j[j,i] <- rnorm(n=1, mean=0, sd=u_j_srf)
    }
    psim[,i] <- boot::inv.logit(b0_srf + usim_j[,i]) 
  }
  
  # frequencies per group and district
  nj1 <- data2[,2]
  nj0 <- data2[,1]
  
  # total n of observations per categorie
  njtotal <- nj1+nj0
  # new frequency distribution for minority
  newcountnj1 <- psim*njtotal
  # new frequency distribution for majority
  newcountnj0 <- njtotal-newcountnj1
  
  # new total of minority observations
  aggrtot1 <- matrix(colSums(newcountnj1),nrow=1)
  # new total of majority observations
  aggrtot0 <- matrix(colSums(newcountnj0),nrow=1)
  
  
  ##############################################
  ################## D ########################
  ############################################
  
  pr1 <- newcountnj1
  pr0 <- newcountnj0
  Dm1 <- rep(0,nsim)
  
  for (i in 1:nsim) {
    pr1[,i] <- newcountnj1[,i]/aggrtot1[,i]
    pr0[,i] <- newcountnj0[,i]/aggrtot0[,i]
    Dm1[i] <- 0.5*sum(abs(pr0[,i]-pr1[,i]))
  }
  
  results <- list("model" = model, "Dm1" = as.vector(Dm1), "r2_1"=as.vector(r2_1), "newcountnj1"=newcountnj1, "newcountnj0"=newcountnj0, "pr1"=pr1, "pr0"=pr0, "aggrtot1"=aggrtot1, "aggrtot0"=aggrtot0, "srf"=srf)
  return(results) 
 


 } else {



######################################################################################################################## 
## THE FOLLOWING CODE IS ONLY USED IN 3-LEVEL MODELS ###################################################################
########################################################################################################################

  #essential the same priniciples as above, so less detailed commenting starting here
 
 # keep relevant data
  form1 <- paste0(group,"~",comp,"+",district1,"+",district2)
  mod <- lm(form1, data=data)
  datanomiss <- mod$model

  #table of distribution across districts
  data21 <- table(datanomiss[,district1],datanomiss[,group])
  data22 <- table(datanomiss[,district2],datanomiss[,group])

  if (ncol(data21)>2) {
    stop("grouping variable has more than two values")
  }

  #number of macro units
  nuj1 <- nrow(data21)
  nuj2 <- nrow(data22)


  #constructing model
  form <- paste0(group,"~",comp,"+(1|",district1,")+(1|",district2,")")


  # null model for scale correction
  form0 <- paste0(group," ~ 1+(1|",district1,")+(1|",district2,")")


  model0 <- glmer(formula=form0, data=datanomiss, family = binomial(link="logit"), nAGQ=0)  
   
  
  # model
  model <- glmer(formula=form, data=datanomiss, family = binomial(link="logit"), nAGQ=0)
   
  
  #total variance null model
  u0_j <- as.data.frame(VarCorr(model0))
  total_var <- 3.29+(u0_j[1,5]^2)+(u0_j[2,5]^2)
  total_var2 <- sqrt(total_var) 
  
  #variance linear predictor
  var_lin <- var(predict(model, re.form=NA))
  
  #scale reduction factor
  srf <- total_var2/sqrt((var_lin+total_var))
  srf <- srf*srf
  
  #saving random effects
  u_j <- as.data.frame(VarCorr(model))
  u_j <- (u_j$sdcor)^2
  
  #apply scale reduction factor
  u_j_srf <- u_j*srf

  # R2 2nd level
  r2_1 <- ((u0_j[1,5]^2)-(u_j_srf[1]))/(u0_j[1,5]^2)
  r2_2 <- ((u0_j[2,5]^2)-(u_j_srf[2]))/(u0_j[2,5]^2)

  #saving intercept
  b0 <- as.numeric(fixef(model)[1])
  
  #apply scale reduction factor
  b0_srf <- b0*srf
  
  u_j_srf <- sqrt(u_j_srf)  

  
  usim_j1 <- matrix(rep(0, nsim*nuj1), nrow=nuj1)
  psim1 <- matrix(rep(0, nsim*nuj1), nrow=nuj1)
  usim_j2 <- matrix(rep(0, nsim*nuj2), nrow=nuj2)
  psim2 <- matrix(rep(0, nsim*nuj2), nrow=nuj2)
  
  for (i in 1:nsim) {
   for (j in 1:nuj1) {
     usim_j1[j,i] <- rnorm(n=1, mean=0, sd=u_j_srf[1])
   }
   for (j in 1:nuj2) {
     usim_j2[j,i] <- rnorm(n=1, mean=0, sd=u_j_srf[2])
   }
  
   psim1[,i] <- inv.logit(b0_srf + usim_j1[,i])
   psim2[,i] <- inv.logit(b0_srf + usim_j2[,i]) 
  }


  
  #frequencies per group and district
  nj11 <- data21[,2]
  nj12 <- data22[,2]
  nj01 <- data21[,1]
  nj02 <- data22[,1]
  
  # total n of observations per category
  njtotal1 <- nj11+nj01
  njtotal2 <- nj12+nj02
  #new frequency distribution for minority
  newcountnj11 <- psim1*njtotal1
  newcountnj12 <- psim2*njtotal2
  #new frequency distribution for majority
  newcountnj01 <- njtotal1-newcountnj11
  newcountnj02 <- njtotal2-newcountnj12
  
  #new total of minority observations
  aggrtot11 <- matrix(colSums(newcountnj11),nrow=1)
  aggrtot12 <- matrix(colSums(newcountnj12),nrow=1)
  #new total of majority observations
  aggrtot01 <- matrix(colSums(newcountnj01),nrow=1)
  aggrtot02 <- matrix(colSums(newcountnj02),nrow=1)
  
  ##############################################
  ################## D ########################
  ############################################
  
  pr11 <- newcountnj11
  pr12 <- newcountnj12
  pr01 <- newcountnj01
  pr02 <- newcountnj02
  Dm1 <- rep(0,nsim)
  Dm2 <- rep(0,nsim)
  
  for (i in 1:nsim) {
    pr11[,i] <- newcountnj11[,i]/aggrtot11[,i]
    pr12[,i] <- newcountnj12[,i]/aggrtot12[,i]
    pr01[,i] <- newcountnj01[,i]/aggrtot01[,i]
    pr02[,i] <- newcountnj02[,i]/aggrtot02[,i]
    Dm1[i] <- 0.5*sum(abs(pr01[,i]-pr11[,i]))
    Dm2[i] <- 0.5*sum(abs(pr02[,i]-pr12[,i]))
  }
  
  # list all results to be returned (can be extend in case additional information for further processing is wanted)
  results <- list("model" = model, "Dm1" = as.vector(Dm1),"Dm2" = as.vector(Dm2), "r2_1"=as.vector(r2_1), "r2_2"=as.vector(r2_2), "newcountnj11"=newcountnj11, "newcountnj12"=newcountnj12, "newcountnj01"=newcountnj01, "newcountnj02"=newcountnj02, "pr11"=pr11, "pr01"=pr01, "pr12"=pr12, "pr02"=pr02, "aggrtot11"=aggrtot11, "aggrtot01"=aggrtot01, "aggrtot12"=aggrtot12, "aggrtot02"=aggrtot02, "srf"=srf)
  return(results)  
  }
}

