@{
    ViewBag.Title = "Customers";
    ViewBag.SitemapProvider = "Modules";
    Layout = "~/Views/Shared/_Folder.cshtml";
}
@model $rootnamespace$.Core.Interfaces.Paging.IPage<$rootnamespace$.Core.Model.Customer>


@if (TempData["Success"] != null)
{                
    <div class="alert alert-success">
        @TempData["Success"]
    </div>
}

<table class="table table-bordered">
    
    @if (this.Model.Entities.Any())
    {
        <thead>
            <tr>
                <th>Customer Name</th>
                <th>Email Address</th>                
                <th>Status</th>
                <th></th>
            </tr>
        </thead>
        
        foreach (var customer in Model.Entities)
        {
            <tr>
                <td>@customer.FullName</td>            
                <td>@customer.EmailAddress</td>
                <td><a href="#">Qualified</a></td>
                <td><a href="@Url.Action("Record", "Customers", new { id = customer.Id })">More Information</a></td>
            </tr>
        }

    }
    else
    {
        <tr>
            <td style="text-align: center">
                <em>There are no customers created yet.  Leads must be created from an external source (See the API Information)</em>
            </td>
        </tr>
    }
    

</table>