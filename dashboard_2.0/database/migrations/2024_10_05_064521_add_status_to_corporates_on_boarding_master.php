<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        Schema::table('corporates_on_boarding_master', function (Blueprint $table) {
            $table->enum('status', ['Active', 'Inactive'])->after('company_domain')->default('Active');
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('corporates_on_boarding_master');
    }
};
