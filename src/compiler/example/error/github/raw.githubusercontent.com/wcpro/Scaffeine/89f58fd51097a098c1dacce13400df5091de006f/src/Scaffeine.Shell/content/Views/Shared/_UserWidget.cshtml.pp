@using $rootnamespace$.Core.Model
<table class="table">
  <tr>
    <td style="width: 50px; border-top: 0">
      <a href="@Url.Action("Photo", "Account")" class="thumbnail">
        <img style="width: 50px" src="@Url.ProfilePicture((string)ViewBag.CurrentUser.PhotoId, "Small", (Gender)ViewBag.CurrentUser.Gender)" class="img-rounded" />
      </a>
    </td>
    <td style="border-top: 0">
      <h4>
        <a href="@Url.Action("Index", "Dashboard")">@ViewBag.CurrentUser.FirstName @ViewBag.CurrentUser.LastName</a>
      </h4>
      <a href="@Url.Action("Profile", "Account")">Edit Profile</a>
    </td>
  </tr>
</table>
