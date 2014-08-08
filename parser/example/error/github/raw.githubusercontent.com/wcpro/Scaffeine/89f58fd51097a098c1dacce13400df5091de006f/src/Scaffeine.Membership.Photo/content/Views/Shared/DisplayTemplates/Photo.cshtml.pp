@using $rootnamespace$.Core.Model
@model string


<img width="50" src="@Url.ProfilePicture(Model, "Small", Gender.Male)"/>