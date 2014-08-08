@{
    ViewBag.Title = "Emails";
    Layout = "~/Views/Shared/_Folder.cshtml";
    ViewBag.SitemapProvider = "Account";
}
@model List<$rootnamespace$.Core.Model.UserEmail>

<table class="table table-bordered">
    <tr>
        <td>@ViewBag.DefaultEmail &nbsp<span class="badge badge-success">Default</span></td>
    </tr>
    
    @foreach (var email in Model)
    {
    <tr>
        <td>@email.EmailAddress
        
            <button class="btn pull-right btn-small">
            Delete
        </button>
        </td>
    </tr>
    }

</table>



@using (Html.BeginForm("Emails", "Account", FormMethod.Post, new { @class = "form-search" }))
{
    @Html.ValidationSummary(true, "Unable to add email.", new { @class = "alert alert-block alert-error" })
    <h4>
    Add another email address</h4>
    <div class="input-append">
        <input type="text" name="EmailAddress" class="span12 search-query">
        <button type="submit" class="btn">Add Email</button>
      </div>
}
