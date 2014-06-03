@using $rootnamespace$.Core.Model
@if (Request.IsAuthenticated)
{
    <div class="btn-group pull-right">
        <a class="btn dropdown-toggle" data-toggle="dropdown" href="#"><i class="">
            <img width="14" src="@Url.ProfilePicture((string)ViewBag.CurrentUser.PhotoId, "Tiny", (Gender)ViewBag.CurrentUser.Gender)" class="img-round" />
        </i> @User.Identity.Name <span class="caret"></span></a>
        <ul class="dropdown-menu">
            <li><a href="@Url.Action("Profile", "Account")">Profile</a></li>          
            <li class="divider"></li>
            <li><a href="@Url.Action("LogOff", "Account")">Sign Out</a></li>
        </ul>
    </div>
}
else
{
    <div class="pull-right">
        <div class="nav-collapse">
            <ul class="nav">
                <li @Html.ActiveWhen("Logon", "Account")><a href="@Url.Action("Logon", "Account")"><i
                    class="icon-user icon-white"></i>Login</a></li>
                <li @Html.ActiveWhen("Register", "Account")><a href="@Url.Action("Register", "Account")">
                    <i class="icon-th-list icon-white"></i>Register</a></li>
            </ul>
        </div>
    </div>

}