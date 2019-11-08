abstract sig Bool{}
sig True extends Bool{}
sig False extends Bool{}

sig Image {
    accepted : one Bool
}

sig LicensePlate{
    modified : one Bool
}

abstract sig AuthenticationType {}
sig SPIDAuthentication extends AuthenticationType {}
sig ProprietaryAuthentication extends AuthenticationType {}

sig Username{}
sig Password{}

sig Authentication {
    authenticationType : one AuthenticationType,
    username : one Username,
    password : one Password
}

sig Name{}
sig Surname{}
sig AuthenticatorID{}

sig Position{}
sig City{
    position : one Position
}

sig FiscalCode{}
sig Address{}
sig PhoneNumber{}
sig Email{}

abstract sig User {
    name : one Name,
    surname : one Surname,
    autheticatorID : one AuthenticatorID,
    authentication : one Authentication,
    reportsMade : set Violation,
    city : one City
}{#authentication.authenticationType=1 or #authentication.authenticationType=2}

sig NormalUser extends User {
    reliabilityScore : one Int,
    birthDate : one Date,
    fiscalCode : one FiscalCode,
    birthLocation : one City,
    phoneNumber : one PhoneNumber,
    address : one Address,
    email : one Email,
    view : one ViolationVisualizerLimited
}{reliabilityScore>=0}

sig Authority extends User {
    authorization : one DigitalCertificateX509,
    notification : set Violation,
    suggestions : set SuggestionsType,
    email : one CertifiedEmail,
    view : ViolationVisualizerPro
}

sig Date{}

sig ID{}
sig DigitalCertificateX509{
    creationDate : one Date,
    dateOfExpiry : one Date,
    id : one ID
} {creationDate!=dateOfExpiry}

sig CertifiedEmail{}

sig VehicleType{}
sig ViolationType{}
sig Note{}

sig Violation{
    violationID : one Int,
    violationType : some ViolationType,
    position : one Position,
    timeStamp : one Date,
    vehicleType: one VehicleType,
    image : one Image,
    licensePlate : one LicensePlate,
    note : one Note,
    email : one Email,
    autheticatorID : one AuthenticatorID,
    verified : one Bool
}{#violationType =< 3 and violationID >= 0}

sig Map{}

abstract sig ViolationVisualizer{
    map : one Map,
    violation : some Violation
}
sig ViolationVisualizerLimited extends ViolationVisualizer{}
sig ViolationVisualizerPro extends ViolationVisualizer{}

sig MunicipalityData {}

--represents Municiplality_i
sig Municipality {
    city : one City,
    incidents : one MunicipalityData
}

sig SuggestionsType {}

sig SuggestionInferralEngine {
    suggestions : some SuggestionsType,
    municipalities : set Municipality
}



fact noDuplicatePasswordNormalUser{
    all u1, u2: NormalUser | (u1.authentication.username = u2.authentication.username and u1.authentication.password = u2.authentication.password) implies u1 = u2
}

fact noDuplicateNormalUser {
    all u1, u2 : NormalUser | (u1.autheticatorID = u2.autheticatorID or u1.fiscalCode = u2.fiscalCode  or u1.email = u2.email
             or u1.authentication = u2.authentication or u1.phoneNumber = u2.phoneNumber) implies u1 = u2
}

fact noDuplicatePasswordAuthority{
    all u1, u2: Authority | (u1.authentication.username = u2.authentication.username) implies u1 = u2
}

fact noDuplicateAuthority {
    all u1, u2 : Authority | u1 = u2
        iff (u1.autheticatorID = u2.autheticatorID  or u1.email = u2.email or u1.authentication = u2.authentication)
}

fact noDuplicateAuthorization{
    all a1, a2 : Authority | a1.authorization = a2.authorization implies a1 = a2
}

fact cityPosition{
	all c1, c2 : City | c1.position = c2.position implies c1 = c2
	all u : User  | some c : City | c = u.city
}

fact noDuplicateDigitalCertificateX509{
	all a1, a2: Authority | a1.authorization.id = a2.authorization.id implies a1.authorization = a2.authorization
	all a : Authority | some c : DigitalCertificateX509 | c = a.authorization
	all c1, c2 : DigitalCertificateX509 | c1 = c2 iff c1.id = c2.id
}

fact noDuplicateViolationsFromUser {
    all v1, v2 : Violation | 
    (v1.timeStamp = v2.timeStamp or v1.email = v2.email or v1.autheticatorID = v2.autheticatorID)
	implies v1.violationID = v2.violationID
	all u : User | some v : Violation | v in u.reportsMade
	all v1, v2 : Violation | v1 = v2 iff v1.violationID = v2.violationID
	all u1, u2 : User | no v : Violation | u1 != u2 and v in u1.reportsMade and v in u2.reportsMade
}

fact noDuplicateViolationsPerUser{
	all u : NormalUser | some v : Violation | v in u.reportsMade implies (v.email = u.email
		and (some a : Authority | v in a.notification))
}

fact noDuplicateViolationTypes {
    all vt, vt', vt'' : ViolationType, v: Violation | 
        ((#v.violationType=3 and vt in v.violationType and vt' in v.violationType and vt'' in v.violationType) 
            implies (vt != vt' and vt' != vt'' and vt != vt'')) or
        ((#v.violationType=2 and vt in v.violationType and vt' in v.violationType) implies (vt != vt'))
}

fact reliabilityScoreInit {
    all u, u' : User | (u!=u' and u.authentication.authenticationType = SPIDAuthentication
        and u'.authentication.authenticationType = ProprietaryAuthentication
        and #u.reportsMade = 0 and #u'.reportsMade = 0) implies (u.reliabilityScore > u'.reliabilityScore)
}

fact verificationManagement{
    all v : Violation | v.verified = False iff v.verified != True
}

fact reliabilityScoreManagement {
    all u, u' : User | u = u' and (some x : Int | x > 0 and (u'.reliabilityScore = u.reliabilityScore + x)) iff
    (some v : Violation | v in u.reportsMade and v.verified = True)
}

--notification
fact notificationFromUserToAuthority{
    all u: User | #u.reportsMade>0 iff (some a : Authority | let r = u.reportsMade | r in a.notification)
}

fact violationNotifier{
    all u : User | some v : Violation | v.email = u.email implies v in u.reportsMade
}

fact notifyWhomManagement{
    all u : User, a : Authority | let r = u.reportsMade | r in a.notification iff (r.position = a.city.position)
}

fact statisticsVisualization{
   all v : ViolationVisualizer | some u : User | v = ViolationVisualizerPro implies u = Authority
   all v : ViolationVisualizer | some u : User | v = ViolationVisualizerLimited implies u = NormalUser
   all v1, v2 : ViolationVisualizer | v1 = v2 iff v1.map = v2.map
}

fact statistics{
    all v : ViolationVisualizer | #v.violation>0 iff (some u : User | #u.reportsMade>0)
}

fact MunicipalityDataManagement{
    all s : SuggestionInferralEngine | #s.suggestions>0 implies (#s.municipalities>0 and (some v : Violation | #v>0))
    all s : SuggestionInferralEngine | all m : Municipality | m in s.municipalities and #m.incidents>0
       and (all m' : Municipality  | ( m.city = m'.city or m.incidents = m'.incidents) iff m = m')
	all m1, m2 : Municipality | m1.city = m2.city implies m1 = m2
}

fact suggestionsActivation{
    all s : SuggestionInferralEngine, v : Violation | #s.suggestions>0 implies (#s.municipalities>0 and #v>0)
}

fact MunicipalityDataProvided{
    all s : SuggestionInferralEngine | (#s.municipalities>0 and (some u : User | #u.reportsMade>0)) 
    implies (some a : Authority | s.suggestions in a.suggestions)
}

pred Registration {
	#NormalUser = 1
	#Authority = 1
}

run Registration for 3 but 0 SuggestionsType, 0 MunicipalityData

pred VisualizerMap {
	#ViolationVisualizerLimited = 1
	#ViolationVisualizerPro = 1
}

run VisualizerMap for 2 but 0 SuggestionsType, 0 MunicipalityData

pred Suggestions{
	#SuggestionInferralEngine = 1
	#Municipality = 2
}
run Suggestions for 3

assert AuthorityRecognition {
	no a : Authority | no c : DigitalCertificateX509 | a.authorization.id = c.id
}
check AuthorityRecognition
