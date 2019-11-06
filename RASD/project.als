abstract sig Bool{}
sig True extends Bool{}
sig False extends Bool{}

sig Username{}

sig Password{}

sig Name{}

sig Surname{}

sig AuthenticatorID{}

sig FiscalCode{}

sig City{}

sig Address{}

sig PhoneNumber{}

sig ID{}

sig Email{}

sig CertifiedEmail extends Email{}

sig DigitalCertificateX509{
    creationDate : one TimeStamp,
    dateOfExpiry : one TimeStamp,
    id : one ID
} {creationDate.milliseconds < dateOfExpiry.milliseconds}

sig ViolationType{}

sig LicensePlate{
    prefixLength: one Int,
    middleLength: one Int,
    suffixLength: one Int,
    modified : one Bool
}{prefixLength=2 and middleLength=3 and suffixLength=2}

sig Position{}

sig Note{
    length : one Int
}{length =< 140 && length > 0}

sig Image {
    modified : one Bool
}

sig Date{ 
    day : one Int,
    month : one Int,
    year : one Int
}{day > 0 and month > 0 and year > 0}

sig TimeStamp extends Date {
    milliseconds : one Int
}{milliseconds>0}

sig Authorization {
    digitalCertificateX509 : one DigitalCertificateX509
}

abstract sig AuthentiaticationType {}
sig SPIDAuthentication extends AuthentiaticationType {}
sig ProprietaryAuthentication extends AuthentiaticationType {}

sig Authentication {
    authenticationType : one AuthentiaticationType,
    username : one Username,
    password : one Password
}

abstract sig User {
    name : one Name,
    surname : one Surname,
    autheticatorID : one AuthenticatorID,
    authentication : one Authentication,
    reportsMade : set Violation
}

sig NormalUser extends User {
    reliabilityScore : one Int,
    birthDate : one Date,
    fiscalCode : one FiscalCode,
    birthLocation : one City,
    phoneNumber : one PhoneNumber,
    city : one City,
    address : one Address,
    email: one Email
}

sig Authority extends User {
    authorization : one Authorization,
    certifiedEmail : one CertifiedEmail,
    notification: set Violation
}

sig Violation {
    violationType : some ViolationType,
    image : one Image,
    licensePlate : one LicensePlate,
    position : one Position,
    timeStamp : one TimeStamp,
    note : one Note,
    email : one Email,
    autheticatorID : one AuthenticatorID,
    verified : one Bool
}{#this.violationType =< 3}

sig ViolationControl {
    reports : some Violation
}

sig Map{}

sig ViolationVisualizer {
    map : one Map
}

abstract sig ViolationLimited {
    violationType : some ViolationType,
    position : one Position,
    timeStamp : one TimeStamp
}

sig ViolationVisualizerLimited extends ViolationVisualizer {
    violationLimited : some ViolationLimited
}

sig ViolationVisualizerPro extends ViolationVisualizer {
    violations : some Violation
}

sig Data{}

sig MunicipalityData {
    data : some Data
}

sig SuggestionInferred {
    municipalityData : one MunicipalityData
}

sig SuggestionInferralEngine {
    suggestions : some SuggestionInferred
}

fact noDuplicateUser {
    no u1, u2 : User | u1! = u2 and u1.autheticatorID = u2.autheticatorID
}

fact noDuplicateAuthenticatorID{
    no u1, u2 : User | u1 = u2 and u1.autheticatorID != u2.autheticatorID
}

fact noDuplicateUsername{
    no u1, u2: User | u1.autheticatorID = u2.autheticatorID
        and u1.authentication.username != u2.authentication.username
}

fact noDuplicatePassword{
    no u1, u2: User | u1.authorization.username = u2.authorization.username
        and u1.authorization.password != u2.authorization.password
}

fact noDuplicatePerson {
    all u1, u2 : NormalUser | u1.autheticatorID != u2.autheticatorID
        implies (u1.fiscalCode != u2.fiscalCode and u1.email != u2.email
            and u1.phoneNumber != u2.phoneNumber)
}

fact noDuplicateAuthority {
    all a1, a2 : Authority | a1.autheticatorID != a2.autheticatorID
    implies a1.certifiedEmail != a2.certifiedEmail
}

fact noDuplicateDigitalCertificateX509 {
    no c1, c2 : DigitalCertificateX509 | c1!=c2 and c1.id = c2.id
}

fact noDuplicateViolationsFromAnUser {
    all v1, v2 : Violation | v1.autheticatorID = v2.autheticatorID
    implies {
        v1.licensePlate != v2.licensePlate => v1.timeStamp.milliseconds - v2.timeStamp.milliseconds < 1200000 
        and v1.position != v2.position
    }
}

fact noDuplicateViolationTypes {
    all vt, vt', vt'' : ViolationType, v: Violation | 
        ((#v.violationType=3 and vt in v.violationType and vt' in v.violationType and vt'' in v.violationType) 
            implies (vt != vt' and vt' != vt'' and vt != vt'')) or
        ((#v.violationType=2 and vt in v.violationType and vt' in v.violationType) => (vt != vt'))
}

fact reliabilityScoreInit {
    all u, u': User | (u!=u' and u.authentication.authenticationType = SPIDAuthentication
        and u'.authentication.authenticationType = ProprietaryAuthentication
        and #u.reportsMade = 0 and #u'.reportsMade = 0) implies (u.reliabilityScore > u'.reliabilityScore)
}

--notification
fact notificationFromUserToAuthority{
    all u: NormalUser | #u.reportsMade>0 implies
        (some a : Authority | u.reportsMade in a.notification)
}

